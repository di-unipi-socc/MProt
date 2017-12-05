/// <reference path="Utils.ts" />
/// <reference path="TOSCA.ts" />
/// <reference path="Analysis.ts" />
/// <reference path="ManagementProtocols.ts" />
var TOSCAAnalysis;
(function (TOSCAAnalysis) {
    var UIData = /** @class */ (function () {
        function UIData(data, uiNames) {
            this.data = data;
            this.uiNames = uiNames;
        }
        return UIData;
    }());
    TOSCAAnalysis.UIData = UIData;
    function toscaString(node, tagName, attr) {
        var nodes = TOSCA.getToscaElements(node, tagName);
        if (nodes.length != 1)
            throw "Invalid format";
        var element = nodes[0];
        return element.getAttribute(attr);
    }
    function toscaMap(node, tagName, attr) {
        var data = {};
        var uiNames = {};
        var nodes = TOSCA.getToscaElements(node, tagName);
        for (var i = 0; i < nodes.length; i++) {
            var element = nodes[i];
            var v = element.getAttribute(attr);
            var id = element.id;
            data[v] = id;
            uiNames[id] = v;
        }
        return new UIData(data, uiNames);
    }
    function mergeNames(a, b) {
        var r = {};
        for (var v in a)
            r[v] = a[v];
        for (var v in b)
            r[v] = b[v];
        return r;
    }
    function mapSet(a, m) {
        var r = {};
        for (var x in a)
            if (x in m)
                r[m[x]] = true;
            else
                console.log("Did not find name for " + x + ". Dropping it");
        return r;
    }
    function mapKeys(a, m) {
        var r = {};
        for (var x in a)
            if (x in m)
                r[m[x]] = a[x];
            else
                console.log("Did not find name for " + x + ". Dropping it");
        return r;
    }
    function handlerReachability(reachable) {
        var visiting = {};
        var visited = {};
        function visit(s) {
            if (visiting[s])
                throw "Cycle in fault handlers detected at " + s;
            if (visited[s])
                return;
            visiting[s] = true;
            for (var s1 in reachable[s]) {
                visit(s1);
                reachable[s] = Utils.setUnion(reachable[s], reachable[s1]);
            }
            delete visiting[s];
            visited[s] = true;
        }
        for (var s in reachable)
            visit(s);
    }
    function handlerTop(reqs, reachable) {
        var top = {};
        for (var s in reachable) {
            top[s] = s;
        }
        for (var t in reachable) {
            for (var s in reachable[t])
                if (Utils.setContains(reqs[t], reqs[top[s]]))
                    top[s] = t;
        }
        return top;
    }
    function computeFaultHandlers(states, handlers, issues) {
        var reqs = {};
        var edges = {};
        var reachable = {};
        var handleReq = {};
        for (var s in states) {
            reqs[s] = states[s].getReqs();
            edges[s] = {};
            reachable[s] = {};
            handleReq[s] = {};
        }
        handlers.forEach(function (handler) {
            var source = states[handler.source];
            var target = states[handler.target];
            if (!Utils.setContains(source.getCaps(), target.getCaps()))
                issues.push({ 'Well-formedness': "Fault handler " + handler.source + " -> " + handler.target + " increases capabilities" });
            else if (!Utils.setContains(reqs[handler.source], reqs[handler.target]))
                issues.push({ 'Well-formedness': "Fault handler " + handler.source + " -> " + handler.target + " increases requirements" });
            else if (Utils.setEquals(reqs[handler.source], reqs[handler.target]))
                issues.push({ 'Well-formedness': "Fault handler " + handler.source + " -> " + handler.target + " preserves requirements" });
            else
                reachable[handler.source][handler.target] = true;
        });
        try {
            handlerReachability(reachable);
        }
        catch (e) {
            issues.push({ 'Well-formedness': e });
        }
        var top = handlerTop(reqs, reachable);
        for (var s in edges)
            for (var t in reachable[top[s]])
                if (Utils.setContains(reqs[s], reqs[t]))
                    edges[s][t] = true;
        // Check transitivity
        // This should never fail, by construction
        for (var s in edges)
            for (var s1 in edges[s])
                for (var s2 in edges[s1])
                    if (!(s2 in edges[s]))
                        issues.push({ 'Race freedom': "Fault handlers " + s + " -> " + s1 + " -> " + s2 + " are not transitive" });
        // Check outgoing handlers
        for (var s in edges)
            for (var s1 in edges[s])
                for (var s2 in edges[s]) {
                    if (s1 == s2)
                        continue;
                    if (Utils.setEquals(reqs[s1], reqs[s2]))
                        issues.push({ 'Determinism': "Fault handlers " + s + " -> " + s1 + "/" + s2 + " are not deterministic" });
                    if (!edges[s1][s2] && Utils.setContains(reqs[s1], reqs[s2]))
                        issues.push({ 'Race freedom': "Fault handlers " + s + " -> " + s1 + " -?> " + s2 + " are not co-transitive" });
                    var intersection = Utils.setIntersection(reqs[s1], reqs[s2]);
                    var union = Utils.setUnion(reqs[s1], reqs[s2]);
                    var foundIntersection = false;
                    var foundUnion = false;
                    for (var s3 in edges[s]) {
                        foundUnion = foundUnion || Utils.setContains(reqs[s3], union);
                        foundIntersection = foundIntersection || Utils.setContains(intersection, reqs[s3]);
                    }
                    if (!foundUnion)
                        issues.push({ 'Race freedom': "Nondeterministic fault handlers " + s + " -> " + s1 + "|" + s2 + " (missing union)" });
                    if (!foundIntersection)
                        issues.push({ 'Race freedom': "Nondeterministic fault handlers " + s + " -> " + s1 + "|" + s2 + " (missing intersection)" });
                }
        for (var s in edges)
            for (var t in edges[s])
                for (var r in Utils.setDiff(reqs[s], reqs[t]))
                    if (!handleReq[s][r] || Utils.setContains(reqs[t], reqs[handleReq[s][r]]))
                        handleReq[s][r] = t;
        return handleReq;
    }
    function nodeTemplateToNode(nodeTemplate, types, sharedIssues) {
        var capNames = toscaMap(nodeTemplate, "Capability", "name");
        var reqNames = toscaMap(nodeTemplate, "Requirement", "name");
        var typeName = nodeTemplate.getAttribute("type").split(':')[1];
        var mProt = new ManagementProtocol.ManagementProtocol(types[typeName]);
        var initialState = mProt.getInitialState();
        var issues = [];
        var states = {};
        var nodeOps = {};
        var protStates = mProt.getStates();
        var handlers = computeFaultHandlers(protStates, mProt.getFaultHandlers(), issues);
        for (var s in protStates) {
            var state = protStates[s];
            var caps = mapSet(state.getCaps(), capNames.data);
            var reqs = mapSet(state.getReqs(), reqNames.data);
            var trans = mProt.getOutgoingTransitions(s);
            var ops = {};
            for (var j = 0; j < trans.length; j++) {
                var opName = trans[j].iface + ":" + trans[j].operation;
                nodeOps[opName] = true;
                var opReqs = mapSet(trans[j].reqs, reqNames.data);
                var prevOp = ops[opName];
                if (prevOp) {
                    if (prevOp.to != trans[j].target) {
                        issues.push({ 'Determinism': "Nondeterministic operation " + s + " -[" + opName + "]-> " + trans[j].target + " / " + prevOp.to });
                    }
                    else {
                        prevOp.reqs.push(opReqs);
                    }
                }
                else {
                    ops[opName] = new Analysis.Operation(trans[j].target, [opReqs]);
                }
            }
            var isAlive = s != initialState;
            states[s] = new Analysis.State(isAlive, caps, reqs, ops, mapKeys(handlers[s] || {}, reqNames.data));
        }
        sharedIssues.push.apply(sharedIssues, issues);
        return new UIData(new Analysis.Node(initialState, typeName, mapSet(mProt.getCaps(), capNames.data), mapSet(mProt.getReqs(), reqNames.data), nodeOps, states, issues.length === 0 ? initialState : null), mergeNames(reqNames.uiNames, capNames.uiNames));
    }
    function serviceTemplateToApplication(serviceTemplate, types, withHardReset) {
        var nodeTemplates = TOSCA.getToscaElements(serviceTemplate, "NodeTemplate");
        var relationships = TOSCA.getToscaElements(serviceTemplate, "RelationshipTemplate");
        var issues = [];
        var reqNodeId = {};
        var capNodeId = {};
        var containedBy = {};
        var nodes = {};
        var binding = {};
        var uiNames = {};
        for (var i = 0; i < nodeTemplates.length; i++) {
            var template = nodeTemplates[i];
            var name = template.getAttribute("name");
            var n = nodeTemplateToNode(template, types, issues);
            var nodeId = template.id;
            nodes[nodeId] = n.data;
            uiNames = mergeNames(uiNames, n.uiNames);
            if (name)
                uiNames[nodeId] = name;
            for (var r in n.data.reqs)
                reqNodeId[r] = nodeId;
            for (var c in n.data.caps)
                capNodeId[c] = nodeId;
        }
        for (var i = 0; i < relationships.length; i++) {
            var rel = relationships[i];
            var req = toscaString(rel, "SourceElement", "ref");
            var cap = toscaString(rel, "TargetElement", "ref");
            binding[req] = cap;
            if (/(^|.*:)[hH]ostedOn$/.test(rel.getAttribute("type"))) {
                var contained = reqNodeId[req];
                var container = capNodeId[cap];
                containedBy[contained] = container;
            }
        }
        return [issues, new UIData(new Analysis.Application(nodes, binding, containedBy, withHardReset), uiNames)];
    }
    TOSCAAnalysis.serviceTemplateToApplication = serviceTemplateToApplication;
    function uiApplicationToElement(app) {
        var setToList = function (x) {
            var list = Object.keys(x);
            if (list.length == 0)
                return "-";
            else
                return list.map(function (s) {
                    return app.uiNames[s] || s;
                }).join("<br>");
        };
        var r = "";
        for (var n in app.data.nodes) {
            var node = app.data.nodes[n];
            // Create a new row for the current node
            r += "<tr class='active row-" + node.type + "'>";
            r += "<td>" + app.uiNames[n] + "</td>";
            r += "<td>" + node.type + "</td>";
            r += "<td>" + setToList(node.caps) + "</td>";
            r += "<td>" + setToList(node.reqs) + "</td>";
            r += "<td>" + setToList(node.ops) + "</td>";
            r += "</tr>";
        }
        return r;
    }
    TOSCAAnalysis.uiApplicationToElement = uiApplicationToElement;
})(TOSCAAnalysis || (TOSCAAnalysis = {}));
