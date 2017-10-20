var BarrelNavBar = React.createClass({
    render: function() {
        return (
            <nav className="navbar navbar-inverse no-margin">
                <div className="container-fluid">
                    <div className="navbar-header">
                        <a className="navbar-brand no-events" href="#">Barrel</a>
                    </div>
                    <div className="collapse navbar-collapse" id="bs-example-navbar-collapse-1">
                        <ul className="nav navbar-nav">
                            {this.props.csar ? <li className="active"><a data-toggle="tab" href="#visualiser">Visualise</a></li> : null}
                            {this.props.csar ? <li><a data-toggle="tab" href="#editor">Edit</a></li> : null}
                            {this.props.csar ? <li><a data-toggle="tab" href="#analyser">Analyse</a></li> : null}
                            <li className="dropdown">
                                <a href="#" className="dropdown-toggle" data-toggle="dropdown" role="button" aria-expanded={false}>CSAR<span className="caret"></span></a>
                                <ul className="dropdown-menu" role="menu">
                                    {this.props.csar ? <li><a href="#" onClick={this.props.exportCsar}>Export</a></li> : null}
                                    <li><a href="#" onClick={() => this.refs.file.click()}>Import
                                        <input ref="file" type="file" onChange={evt => this.props.onChange(evt.target.files[0])} style={{ display: "none" }} />
                                    </a></li>
                                </ul>
                            </li>
                        </ul>
                        <ul className="nav navbar-nav navbar-right">
                            <li><a data-toggle="modal" data-target="#modal-info">About</a></li>
                        </ul>
                    </div>
                </div>
            </nav>
        );
    }
});

var SingleSelector = React.createClass({
    getInitialState: function() {
        return {
            selected: this.props.value,
        };
    },

    componentWillReceiveProps: function(nextProps) {
        this.setState({
            selected: nextProps.value,
        });
    },

    render: function() {
        var makeOption = v => <option key={v} value={v}>{v}</option>;
        var onChange = evt => {
            this.setState({ selected: evt.target.value });
            if (this.props.onChange)
                this.props.onChange(evt.target.value);
        };

        return (
            <select className="form-control" value={this.state.selected} onChange={onChange}>
                {Object.keys(this.props.items).map(makeOption)}
            </select>
        );
    }
});

var MultiSelector =  React.createClass({
    render: function() {
        var makeCheckBox = (v) => (
            <label key={v}>
                <input type="checkbox" checked={this.props.values(v)} onChange={evt => this.props.onChange(v, evt.target.checked)} />
                {v}
            </label>
        );

        return <div>{Object.keys(this.props.items).map(makeCheckBox)}</div>;
    }
});

var BarrelStateCREditor = React.createClass({
    makeState: function(props) {
        if (this.state && this.state.selectedState in props.editor.state.mProt.getStates())
            return this.state;
        else
            return {
                selectedState: props.editor.state.mProt.getInitialState()
            };
    },

    getInitialState: function() {
        return this.makeState(this.props);
    },

    componentWillReceiveProps: function(nextProps) {
        this.setState(this.makeState(nextProps));
    },

    render: function() {
        var mProt = this.props.editor.state.mProt
        var reqs = mProt.getReqs();
        var caps = mProt.getCaps();
        var states = mProt.getStates();
        var state = states[this.state.selectedState];
        var stateReqs = state.getReqs();
        var stateCaps = state.getCaps();

        var setReq = (r, value) => {
            if (value)
                stateReqs[r] = true;
            else
                delete stateReqs[r];

            state.setReqs(stateReqs);
            this.setState(this.state);
            this.props.editor.refresh();
        };

        var setCap = (c, value) => {
            if (value)
                stateCaps[c] = true;
            else
                delete stateCaps[c];

            state.setCaps(stateCaps);
            this.setState(this.state);
            this.props.editor.refresh();
        };

        return (
            <div className="modal-dialog">
                <div className="modal-content">
                    <div className="modal-header">
                        <button type="button" className="close" data-dismiss="modal" aria-hidden="true">&times;</button>
                        <h4 className="modal-title">State</h4>
                    </div>
                    <div className="modal-body">
                        <label className="control-label">State:</label>
                        <SingleSelector
                            value={this.state.selectedState}
                            items={states}
                            onChange={s => this.setState({ selectedState: s })} />
                        <label className="control-label">Requirements held:</label>
                        <MultiSelector items={reqs} values={r => r in stateReqs} onChange={setReq} />
                        <label className="control-label">Capabilities provided:</label>
                        <MultiSelector items={caps} values={r => r in stateCaps} onChange={setCap} />
                    </div>
                </div>
            </div>
        );
    }
});

var BarrelTransitionAdder = React.createClass({
    makeState: function(props) {
        var states = Object.keys(props.editor.state.mProt.getStates());
        var ops = props.editor.state.mProt.getOps();
        return {
            source: states[0],
            target: states[0],
            iface: ops[0].iface,
            operation: ops[0].operation,
            reqs: {}
        };
    },

    getInitialState: function() {
        return this.makeState(this.props);
    },

    componentWillReceiveProps: function(nextProps) {
        this.setState(this.makeState(nextProps));
    },

    render: function() {
        var mProt = this.props.editor.state.mProt;
        var reqs = mProt.getReqs();
        var states = mProt.getStates();
        var mergeOp = o => o.iface + ":" + o.operation;
        var ops = Utils.makeSet(mProt.getOps().map(mergeOp));

        var splitOp = s => {
            var o = s.split(":", 2);
            return { iface: o[0], operation: o[1] };
        };

        var setReq = (r, value) => {
            if (value)
                this.state.reqs[r] = true;
            else
                delete this.state.reqs[r];

            this.setState(this.state);
        };

        var apply = () => {
            this.props.editor.state.mProt.addTransition(this.state);
            this.props.editor.refresh();
        };

        return (
            <div className="modal-dialog">
                <div className="modal-content">
                    <div className="modal-header">
                        <button type="button" className="close" data-dismiss="modal" aria-hidden="true">&times;</button>
                        <h4 className="modal-title">Add transition</h4>
                    </div>
                    <div className="modal-body">
                        <label className="control-label">Starting state:</label>
                        <SingleSelector
                            value={this.state.source}
                            items={states}
                            onChange={s => this.setState({ source: s })} />
                        <label className="control-label">Operation:</label>
                        <SingleSelector
                            value={mergeOp(this.state)}
                            items={ops}
                            onChange={s => this.setState(splitOp(s))} />
                        <label className="control-label">Target state:</label>
                        <SingleSelector
                            value={this.state.target}
                            items={states}
                            onChange={s => this.setState({ target: s })} />
                        <label className="control-label">Requirements held:</label>
                        <MultiSelector items={reqs} values={r => r in this.state.reqs} onChange={setReq} />
                    </div>
                    <div className="modal-footer">
                        <button type="button" className="btn btn-default" data-dismiss="modal">Close</button>
                        <button type="button" className="btn btn-primary" data-dismiss="modal" onClick={apply}>Apply</button>
                    </div>
                </div>
            </div>
        );
    }
});

var BarrelTransitionRemover = React.createClass({
    makeState: function(props, baseState) {
        var trans = props.editor.state.mProt.getTransitions();
        if (trans.length == 0) return {
            source: "",
            target: "",
            iface: "",
            operation: "",
            reqs: {}
        };

        var sameSource = trans.filter(t => t.source == baseState.source);
        if (sameSource.length == 0) return trans[0];

        var sameOp = sameSource.filter(t => t.iface == baseState.iface && t.operation == baseState.operation);
        if (sameOp.length == 0) return sameSource[0];

        var sameTarget = sameOp.filter(t => t.target == baseState.target);
        if (sameTarget.length == 0) return sameOp[0];

        var sameReqs = sameTarget.filter(t => Utils.setEquals(t.reqs == baseState.reqs));
        if (sameReqs.length == 0) return sameTarget[0];

        return sameReqs[0];
    },

    getInitialState: function() {
        return this.makeState(this.props, {});
    },

    componentWillReceiveProps: function(nextProps) {
        this.setState(this.makeState(nextProps, {}));
    },

    setStateAndComputeDeps: function(nextState) {
        for (var k in this.state)
            if (!(k in nextState))
                nextState[k] = this.state[k];
        this.setState(this.makeState(this.props, nextState));
    },

    render: function() {
        var mProt = this.props.editor.state.mProt;
        var trans = mProt.getTransitions();
        var states = Utils.makeSet(trans.map(t => t.source));
        var sameSource = trans.filter(t => t.source == this.state.source);
        var sameOp = sameSource.filter(t => t.iface == this.state.iface && t.operation == this.state.operation);
        var sameTarget = sameOp.filter(t => t.target == this.state.target);

        var splitOp = s => {
            var o = s.split(":", 2);
            return { iface: o[0], operation: o[1] };
        };
        var mergeOp = o => o.iface + ":" + o.operation;
        var ops = Utils.makeSet(sameSource.map(mergeOp));
        var currOp = mergeOp(this.state);

        var targets = Utils.makeSet(sameOp.map(t => t.target));

        var splitReqs = s => Utils.makeSet(s.split("+"));
        var mergeReqs = reqSet => {
            var reqList = Object.keys(reqSet);
            reqList.sort();
            return reqList.join("+");
        };
        var currReqs = mergeReqs(this.state.reqs);
        var reqs = Utils.makeSet(sameTarget.map(t => mergeReqs(t.reqs)));

        var apply = () => {
            this.props.editor.state.mProt.removeTransition(this.state)
            this.props.editor.refresh();
        };

        return (
            <div className="modal-dialog">
                <div className="modal-content">
                    <div className="modal-header">
                        <button type="button" className="close" data-dismiss="modal" aria-hidden="true">&times;</button>
                        <h4 className="modal-title">Remove transition</h4>
                    </div>
                    <div className="modal-body">
                        <label className="control-label">Starting state:</label>
                        <SingleSelector
                            value={this.state.source}
                            items={states}
                            onChange={s => this.setStateAndComputeDeps({ source: s })} />
                        <label className="control-label">Operation:</label>
                        <SingleSelector
                            value={currOp}
                            items={ops}
                            onChange={s => this.setStateAndComputeDeps(splitOp(s))} />
                        <label className="control-label">Target state:</label>
                        <SingleSelector
                            value={this.state.target}
                            items={targets}
                            onChange={s => this.setStateAndComputeDeps({ target: s })} />
                        <label className="control-label">Requirements:</label>
                        <SingleSelector
                            value={currReqs}
                            items={reqs}
                            onChange={s => this.setStateAndComputeDeps({ reqs: splitReqs(s) })} />
                    </div>
                    <div className="modal-footer">
                        <button type="button" className="btn btn-default" data-dismiss="modal">Close</button>
                        <button type="button" className="btn btn-primary" data-dismiss="modal" onClick={apply}>Apply</button>
                    </div>
                </div>
            </div>
        );
    }
});

var BarrelFaultAdder = React.createClass({
    makeState: function(props) {
        var states = Object.keys(props.editor.state.mProt.getStates());
        return {
            source: states[0],
            target: states[0]
        };
    },

    getInitialState: function() {
        return this.makeState(this.props);
    },

    componentWillReceiveProps: function(nextProps) {
        this.setState(this.makeState(nextProps));
    },

    render: function() {
        var states = this.props.editor.state.mProt.getStates();

        var apply = () => {
            this.props.editor.state.mProt.addFaultHandler(this.state);
            this.props.editor.refresh();
        };

        return (
            <div className="modal-dialog">
                <div className="modal-content">
                    <div className="modal-header">
                        <button type="button" className="close" data-dismiss="modal" aria-hidden="true">&times;</button>
                        <h4 className="modal-title">Add fault handler</h4>
                    </div>
                    <div className="modal-body">
                        <label className="control-label">Starting state:</label>
                        <SingleSelector
                            value={this.state.source}
                            items={states}
                            onChange={s => this.setState({ source: s })} />
                        <label className="control-label">Target state:</label>
                        <SingleSelector
                            value={this.state.target}
                            items={states}
                            onChange={s => this.setState({ target: s })} />
                    </div>
                    <div className="modal-footer">
                        <button type="button" className="btn btn-default" data-dismiss="modal">Close</button>
                        <button type="button" className="btn btn-primary" data-dismiss="modal" onClick={apply}>Apply</button>
                    </div>
                </div>
            </div>
        );
    }
});

var BarrelFaultRemover = React.createClass({
    makeState: function(props, baseState) {
        var handlers = props.editor.state.mProt.getFaultHandlers();
        if (handlers.length == 0) return { source: "", target: "" };

        var sameSource = handlers.filter(h => h.source == baseState.source);
        if (sameSource.length == 0) return handlers[0];

        var sameTarget = sameSource.filter(h => h.target == baseState.target);
        if (sameTarget.length == 0) return sameSource[0];

        return sameTarget[0];
    },

    getInitialState: function() {
        return this.makeState(this.props, {});
    },

    componentWillReceiveProps: function(nextProps) {
        this.setState(this.makeState(nextProps, {}));
    },

    setSource: function(source) {
        this.state.source = source;
        this.setState(this.makeState(this.props, this.state));
    },

    render: function() {
        var mProt = this.props.editor.state.mProt;
        var handlers = mProt.getFaultHandlers();
        var sources = Utils.makeSet(handlers.map(h => h.source));
        var targets = Utils.makeSet(handlers.filter(h => h.source == this.state.source).map(h => h.target));

        var apply = () => {
            this.props.editor.state.mProt.removeFaultHandler(this.state)
            this.props.editor.refresh();
        };

        return (
            <div className="modal-dialog">
                <div className="modal-content">
                    <div className="modal-header">
                        <button type="button" className="close" data-dismiss="modal" aria-hidden="true">&times;</button>
                        <h4 className="modal-title">Remove fault handler</h4>
                    </div>
                    <div className="modal-body">
                        <label className="control-label">Starting state:</label>
                        <SingleSelector
                            value={this.state.source}
                            items={sources}
                            onChange={s => this.setSource(s)} />
                        <label className="control-label">Target state:</label>
                        <SingleSelector
                            value={this.state.target}
                            items={targets}
                            onChange={s => this.setState({ target: s })} />
                    </div>
                    <div className="modal-footer">
                        <button type="button" className="btn btn-default" data-dismiss="modal">Close</button>
                        <button type="button" className="btn btn-primary" data-dismiss="modal" onClick={apply}>Apply</button>
                    </div>
                </div>
            </div>
        );
    }
});

var BarrelMProtGraphState = React.createClass({
    render: function() {
        var makeDraggable = el => { if (el) jsPlumb.draggable(el, { containment: "parent" }); };

        return (
            <div
                ref={makeDraggable}
                id={"state_" + this.props.name}
                className={"stateDiv" + (this.props.initial ? " initial" : "")}
                style={{ left: this.props.left, top: this.props.top }}>
                <div>{this.props.name}</div>
                <div className="reliesOnOffersDiv">
                    Relies on:
                    {Object.keys(this.props.state.getReqs()).map(x => <div key={x}>- {x}</div>)}
                </div>
                <div className="reliesOnOffersDiv">
                    Offers:
                    {Object.keys(this.props.state.getCaps()).map(x => <div key={x}>- {x}</div>)}
                </div>
            </div>
        );
    }
});

var BarrelMProtGraph = React.createClass({
     drawTransitions: function() {
        this.props.mProt.getTransitions().forEach(transition => {
            var sourceState = "state_" + transition.source;
            var targetState = "state_" + transition.target;
            var transLabel = "<b>" + transition.iface + ":" + transition.operation + "</b>";
            var reqs = Object.keys(transition.reqs);
            reqs.sort();

            if (reqs.length != 0)
                transLabel += "<br> Relies on: {" + reqs.join(", ") + "}";

            jsPlumb.connect({
                source: sourceState,
                target: targetState,
                anchor: "Continuous",
                connector: ["StateMachine", { curviness: 50 }],
                endpoint: "Blank",
                paintStyle: { strokeStyle: "#112835", lineWidth: 2 },
                hoverPaintStyle: { strokeStyle: "#3399FF" },
                overlays: [
                    ["Arrow", { location: 1 }],
                    ["Label", { label: transLabel, id: "label", location: 0.4, cssClass: "transLabel" }]
                ]
            });
        });
    },

    drawHandlers: function() {
        this.props.mProt.getFaultHandlers().forEach(handler => {
            var sourceState = "state_" + handler.source;
            var targetState = "state_" + handler.target;

            jsPlumb.connect({
                source: sourceState,
                target: targetState,
                anchor: "Continuous",
                connector: ["StateMachine", { curviness: 50 }],
                endpoint: "Blank",
                paintStyle: { strokeStyle: "#95a5a6", lineWidth: 2 },
                hoverPaintStyle: { strokeStyle: "#3399FF" },
                overlays: [["Arrow", { location: 1 }]]
            });
        });
    },

    render: function() {
        jsPlumb.reset();

        // TODO: refactor layout computation
        var firstRow = true;
        var x = 20;
        var y = 20;
        var deltaX = ($(window).width() - 200) / 4;
        var deltaY = ($(window).height() - 100) / 2;

        var mProt = this.props.mProt;
        var instanceStates = mProt.getStates();
        var initialState = mProt.getInitialState();

        var states = [];
        for (var s in instanceStates) {
            states.push(
                <BarrelMProtGraphState
                    key={s}
                    name={s}
                    state={instanceStates[s]}
                    initial={initialState == s}
                    left={x + "px"}
                    top={y + "px"} />
            );

            firstRow = !firstRow;
            if (firstRow) {
                x = (x + deltaX);
                y = 20;
            } else {
                y = y + deltaY;
            }
        }

        var redrawConnections = () => {
            jsPlumb.getConnections().forEach(c => jsPlumb.detach(c));
            this.drawTransitions();
            this.drawHandlers();
            jsPlumb.repaintEverything();
        };

        return <div ref={redrawConnections} className="mprot-graph">{states}</div>;
    }
});

var BarrelEditor = React.createClass({
    getInitialState: function() {
        return this.makeState(Object.keys(this.props.typeDocs)[0]);
    },

    makeState: function(name) {
        return {
            name: name,
            mProt: new ManagementProtocol.ManagementProtocolEditor(this.props.typeDocs[name], name)
        };
    },

    setType: function(name) {
        this.setState(this.makeState(name));
        this.refresh();
    },

    refresh: function() {
        this.state.mProt.save(() => {
            this.refs.mProtGraph.forceUpdate();
            this.props.onChange();
        });
    },

    render: function() {
        var exportXMLDoc = () => {
            var url = URL.createObjectURL(this.state.mProt.getXML());
            window.open(url, "_blank", "");
        };

        var types = Object.keys(this.props.typeDocs).map(t => <li key={t}><a href="#" onClick={() => this.setType(t)}>{t}</a></li>);

        return (
            <div>
              <h1>Management protocol editor</h1>
              <div className="form-horizontal node-type-selector">
                Node type:
                <SingleSelector
                  value={this.state.name}
                  items={this.props.typeDocs}
                  onChange={newType => this.setType(newType)}/>
                {this.props.issues.map((x, i) => (<span key={i}>✘ {x}</span>))}
                <a className="btn btn-info" onClick={exportXMLDoc}>Show XML</a>
              </div>
              <div className="form-horizontal">
                <pre><BarrelMProtGraph ref="mProtGraph" mProt={this.state.mProt} /> </pre>
              </div>
              <div className="form-horizontal">
                <div className="col-sm-4">
                  <h4>Initial state</h4>
                  <SingleSelector
                    value={this.state.mProt.getInitialState()}
                    items={this.state.mProt.getStates()}
                    onChange={newInitialState => {
                      this.state.mProt.setInitialState(newInitialState);
                      this.refresh();
                    }} />
                    <h4>States</h4>
                    <div className="btn-group btn-group-justified">
                      <a className="btn btn-primary" data-toggle="modal" data-target="#modal-state-editor">Edit</a>
                    </div>
                </div>
                <div className="col-sm-4">
                  <h4>Transitions</h4>
                  <div className="btn-group btn-group-justified">
                    <a className="btn btn-primary" data-toggle="modal" data-target="#modal-add-transition-editor">Add</a>
                    <a className="btn btn-primary"    data-toggle="modal" data-target="#modal-remove-transition-editor">Remove</a>
                  </div>
                  <h4>Fault handlers</h4>
                  <div className="btn-group btn-group-justified">
                    <a className="btn btn-primary" data-toggle="modal" data-target="#modal-add-fault-editor">Add</a>
                    <a className="btn btn-primary"    data-toggle="modal" data-target="#modal-remove-fault-editor">Remove</a>
                  </div>
                </div>
                <div className="col-sm-4">
                  <h4>Default handling</h4>
                  <div className="btn-group btn-group-justified">
                    <a className="btn btn-primary" onClick={() => {
                      try { this.state.mProt.addState("Crashed"); } catch (e) {};
                        this.state.mProt.addDefaultHandling("Crashed");
                        this.refresh();
                      }}>Fault</a>
                    <a className="btn btn-primary" onClick={() => {
                      try { this.state.mProt.addState("Crashed"); } catch (e) {};
                      try { this.state.mProt.addOperation("Special", "Crash"); } catch (e) {};
                        this.state.mProt.addCrashOps("Crashed", "Special", "Crash");
                        this.refresh();
                      }}>Crashes</a>
                  </div>
                </div>
              </div>
              <div id="modal-state-editor" className="modal fade">
                  <BarrelStateCREditor editor={this} />
              </div>
              <div id="modal-add-transition-editor" className="modal fade">
                  <BarrelTransitionAdder editor={this} />
              </div>
              <div id="modal-remove-transition-editor" className="modal fade">
                  <BarrelTransitionRemover editor={this} />
              </div>
              <div id="modal-add-fault-editor" className="modal fade">
                  <BarrelFaultAdder editor={this} />
              </div>
              <div id="modal-remove-fault-editor" className="modal fade">
                  <BarrelFaultRemover editor={this} />
              </div>
            </div>
        );
    }
});

var BarrelTabs = React.createClass({
    getInitialState() {
        return { hardReset: false };
    },

    render: function() {
        var csar = this.props.csar;
        var serviceTemplate = csar.get("ServiceTemplate")[0].element;
        var types = csar.getTypes();
        var [issues, uiData] = TOSCAAnalysis.serviceTemplateToApplication(serviceTemplate, types, this.state.hardReset);

        const issueKeys = {};
        const issuesStrings = [];
        for (const o of issues) {
            const key = Object.keys(o)[0];
            issueKeys[key] = true;
            issuesStrings.push(`${key}: ${o[key]}`);
        }

        var analyser = issues.length !== 0
            ? (
                <div>
                    <h1>Invalid application</h1>
                    The application cannot be analysed because:
                    <ul>
                    { issuesStrings.map((o, i) => (<li key={i}>{o}</li>)) }
                    </ul>
                </div>
            )
            : (
                <div>
                    <div>
                        <h1 className="bolded">Options</h1>
                        <Opt
                            caption="Hard recovery"
                            enabled={this.state.hardReset}
                            onClick={() => this.setState({ hardReset: !this.state.hardReset })} />
                    </div>
                    <br />
                    <Analyser
                        uiData={uiData}
                        reachable={Analysis.reachable(uiData.data)}
                        plans={Analysis.plans(uiData.data)} />
                </div>
            );

        return (
            <div className="container" style={{ backgroundColor: "white" }}>
                <div className="tab-content">
                    <div className="tab-pane active" id="visualiser">
                        <Visualiser
                            uiData={uiData}
                            nodeTypes={types}
                            appName={serviceTemplate.getAttribute("name")} />
                    </div>
                    <div className="tab-pane" id="editor">
                        <BarrelEditor issues={Object.keys(issueKeys)} typeDocs={csar.getTypeDocuments()} onChange={() => this.forceUpdate()} />
                    </div>
                    <div className="tab-pane" id="analyser">
                        {analyser}
                    </div>
                </div>
            </div>
        );
    }
});

var BarrelMain = React.createClass({
    getInitialState: function() {
        return {
            csarFileName: "",
            csar: null
        };
    },

    render: function() {
        var saveBlob = blob => saveAs(blob.slice(0, blob.size, "application/octet-stream"), this.state.csarFileName, true);
        var exportCsar = () => this.state.csar.exportBlob(saveBlob);

        var readCsar = file => {
            this.setState({ csarFileName: file.name });
            var tmpCsar = new Csar.Csar(file, () => this.setState({ csar: tmpCsar }));
        };

        return (
            <div>
                <BarrelNavBar csar={this.state.csar} onChange={readCsar} exportCsar={exportCsar} />
                {this.state.csar ? <BarrelTabs csar={this.state.csar} /> : null}
            </div>
        );
    }
});

barrel = ReactDOM.render(<BarrelMain />, document.getElementById('main'));
