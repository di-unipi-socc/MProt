var Operations = React.createClass({
  render: function() {
    var ops = this.props.nodeType.getElementsByTagName("Operation");
    var opString = op =>
      op.parentElement.getAttribute("name")+":"+op.getAttribute("name");
    return (
      <span>
        {$.map(ops, op => (
          <span key={this.props.nodeId+"-"+opString(op)}>
            {opString(op)}
            <br />
          </span>))}
      </span>
    )
  }
})

var TopologyRow = React.createClass({
  render: function() {
    var renderSet = set => Object.keys(set).map(el => <span key={el}>{this.props.getUIName(el)}<br /></span>);
    return (
        <tr>
            <td><b>{this.props.getUIName(this.props.nodeId)}</b></td>
            <td>{this.props.node.type}</td>
            <td>{renderSet(this.props.node.caps)}</td>
            <td>{renderSet(this.props.node.reqs)}</td>
            <td><Operations nodeId={this.props.nodeId} nodeType={this.props.nodeType} /></td>
        </tr>
    );
  }
})

var TopologyTable = React.createClass({
  render: function() {
    // Setting the stage
    var getUIName = id => this.props.uiData.uiNames[id] || id;

  	var nodes = this.props.uiData.data.nodes;
    // Rendering
  	return (
      <table className="table table-striped table-hover">
        <thead>
            <tr className="btn-primary disabled">
                <th>Node</th>
                <th>Node type</th>
                <th>Capabilities</th>
                <th>Requirements</th>
                <th>Operations</th>
            </tr>
        </thead>
        <tbody>{
          Object.keys(nodes).map(id =>
            <TopologyRow
                key={id}
                getUIName={getUIName}
                nodeId={id}
                node={nodes[id]}
                nodeType={this.props.nodeTypes[nodes[id].type]}
            />)
        }</tbody>
      </table>
    );
  }
});

Visualiser = React.createClass({
  render: function() {
        var createGraph = function(parentElement, width, height) {
            // Create the "joint.dia.Graph" to be returned
            var graph = new joint.dia.Graph();

            // Create a "joint.dia.Paper" environment (inside "parentElement") where to place the graph
            var paper = new joint.dia.Paper({
                el: parentElement,
                width: width,
                height: height,
                model: graph
            });

            // Avoid inner elements to overflow the environment
            paper.on('cell:pointermove', function (cellView, evt, x, y) {
                var cell = cellView.getBBox();
                var constrained = false;

                var constrainedX = x;
                if (cell.x <= 0) { constrainedX = x + 1; constrained = true }
                if (cell.x + cell.width >= width) { constrainedX = x - 1; constrained = true }

                var constrainedY = y;
                if (cell.y <= 0) { constrainedY = y + 1; constrained = true }
                if (cell.y + cell.height >= height) { constrainedY = y - 1; constrained = true }

                if (constrained) { cellView.pointermove(evt, constrainedX, constrainedY) }
            });

            // Return the created "joint.dia.Graph"
            return { graph: graph, paper: paper };
        };

        var drawTopology = function(parentDiv, topology) {
            if (parentDiv == null)
                return;
            parentDiv.innerHTML = "";

            var nodes = topology.data.nodes;
            var cells = {};

            var toUI = function (s) { return topology.uiNames[s] || s; };

            var TopologyNode = joint.shapes.basic.Generic.extend(_.extend({}, joint.shapes.basic.PortsModelInterface, {
                markup: '<g class="rotatable"><g class="scalable"><rect class="body"/></g><text class="label"/><g class="inPorts"/><g class="outPorts"/></g>',
                portMarkup: '<g class="port port<%= id %>"><circle class="port-body"/><text class="port-label"/></g>',
                defaults: joint.util.deepSupplement({
                type: 'devs.Model',
                size: { width: 1, height: 1 },
                inPorts: [],
                outPorts: [],
                attrs: {
                    '.': { magnet: false },
                    '.body': { width: 150, height: 50, 'rx': 10, 'ry': 5 },
                    '.port-body': { r: 8, magnet: 'passive' },
                    text: { 'pointer-events': 'none' },
                    '.label': { text: 'Model', 'ref-x': .5, 'ref-y': 18, ref: '.body', 'text-anchor': 'middle' },
                    '.inPorts .port-label': { x: 4, y: -9, 'text-anchor': 'start', transform: 'rotate(330)' },
                    '.outPorts .port-label': { x: 1, y: 19, 'text-anchor': 'end', transform: 'rotate(330)' }
                }
                }, joint.shapes.basic.Generic.prototype.defaults),
                getPortAttrs: function (portName, index, total, selector, type) {
                var attrs = {};
                var portClass = 'port' + index;
                var portSelector = selector + '>.' + portClass;
                var portLabelSelector = portSelector + '>.port-label';
                var portBodySelector = portSelector + '>.port-body';
                attrs[portLabelSelector] = { text: toUI(portName) };
                attrs[portBodySelector] = { port: { id: portName || _.uniqueId(type), type: type } };
                attrs[portSelector] = { ref: '.body', 'ref-x': (index + 0.5) * (1 / total) };
                if (selector === '.outPorts') {
                    attrs[portSelector]['ref-dy'] = 0;
                }
                return attrs;
                }
            }));

            // Create a new environment (see createGraph function definition)
            var graphWidth = 940;
            var containers = document.getElementsByClassName("container");
            if (containers.length) graphWidth = containers[0].offsetWidth - 30;
            var env = createGraph(parentDiv, graphWidth, 600);

            // Create a cell for each node
            for (var n in nodes) {
                var name = toUI(n);
                var caps = Object.keys(nodes[n].caps);
                var reqs = Object.keys(nodes[n].reqs);

                // Compute ad-hoc size for
                var nWidth = 20 + Math.max(
                Math.max(caps.length, reqs.length) * 20,
                name.length * 10);
                var nHeight = 50;

                // Create cells[n], and add it to env.graph
                cells[n] = new TopologyNode({
                size: { width: nWidth, height: nHeight },
                inPorts: caps,
                outPorts: reqs,
                attrs: { '.label': { text: name } }
                }).addTo(env.graph);

                // Replicate "type" information in "cell" to simplify double-click handling
                cells[n].nodeType = nodes[n].type
            }

            // Create connections among node cells according to the parsed topology
            for (var nodeId in nodes) {
                for (var req in nodes[nodeId].reqs) {
                var source = cells[nodeId];
                var sourcePort = req;
                var targetPort = topology.data.binding[req];
                var target = cells[topology.data.capNodeId[targetPort]];
                new joint.shapes.devs.Link({
                    source: { id: source.id, selector: source.getPortSelector(sourcePort) },
                    target: { id: target.id, selector: target.getPortSelector(targetPort) },
                    smooth: true,
                    attrs: { '.marker-target': { d: 'M 10 0 L 0 5 L 10 10 z' } }
                }).addTo(env.graph).reparent();
                }
            }

            // Layout the graph as a DAG
            joint.layout.DirectedGraph.layout(env.graph, {
                marginX: 50,
                marginY: 50,
                rankDir: "TB" });
        };

    return (
        <div>
            <h1 className="legend bolded">
            {this.props.appName || "Unnamed"}
            </h1>
            <h4>Application topology</h4>
            <div>
              <div style={{verticalAlign: "top", display:"inline-block"}}>
                <div ref={el => drawTopology(el, this.props.uiData)}></div>
              </div>
              <div style={{fontSize:"90%", verticalAlign: "top", display:"inline-block"}}>
                <TopologyTable uiData={this.props.uiData} nodeTypes={this.props.nodeTypes}/>
              </div>
            </div>
        </div>
    );
  }
});
