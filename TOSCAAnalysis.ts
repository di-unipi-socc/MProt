/// <reference path="Utils.ts" />
/// <reference path="TOSCA.ts" />
/// <reference path="Analysis.ts" />
/// <reference path="ManagementProtocols.ts" />

module TOSCAAnalysis {
    export interface UINames { [id: string]: string }

    export class UIData<T> {
        constructor(public data: T,
            public uiNames: UINames) { }
    }

    function toscaString(node: Element, tagName: string, attr: string) {
        var nodes = TOSCA.getToscaElements(node, tagName);
        if (nodes.length != 1)
            throw "Invalid format";

        var element = <Element>nodes[0];
        return element.getAttribute(attr);
    }

    function toscaMap(node: Element, tagName: string, attr: string) {
        var data: Utils.Map<string> = {};
        var uiNames: UINames = {};
        var nodes = TOSCA.getToscaElements(node, tagName);
        for (var i = 0; i < nodes.length; i++) {
            var element = <HTMLElement>nodes[i];
            var v = element.getAttribute(attr);
            var id = element.id;
            data[v] = id;
            uiNames[id] = v;
        }

        return new UIData(data, uiNames);
    }

    function mergeNames(a: UINames, b: UINames) {
        var r: UINames = {};
        for (var v in a)
            r[v] = a[v];
        for (var v in b)
            r[v] = b[v];
        return r;
    }

    function mapSet(a: Utils.Set, m: Utils.Map<string>) {
        var r: Utils.Set = {};
        for (var x in a)
            if (x in m)
                r[m[x]] = true;
            else
                console.log("Did not find name for " + x  + ". Dropping it");

        return r;
    }

    function mapKeys<T>(a: Utils.Map<T>, m: Utils.Map<string>) {
        var r: Utils.Map<T> = {};
        for (var x in a)
            if (x in m)
                r[m[x]] = a[x];
            else
                console.log("Did not find name for " + x  + ". Dropping it");

        return r;
    }

    function handlerReachability(reachable : Utils.Map<Utils.Set>) {
        var visiting : Utils.Set = {};
        var visited : Utils.Set = {};
        function visit(s) {
            if (visiting[s])
                throw `Cycle in fault handlers detected at ${s}`;
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

    function handlerTop(reqs: Utils.Map<Utils.Set>, reachable: Utils.Map<Utils.Set>) {
        var top: Utils.Map<string> = {};
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

    function computeFaultHandlers(states: Utils.Map<ManagementProtocol.State>, handlers: ManagementProtocol.FaultHandler[], issues: any[]) {
        var reqs: Utils.Map<Utils.Set> = {};
        var edges: Utils.Map<Utils.Set> = {};
        var reachable: Utils.Map<Utils.Set> = {};
        var handleReq: Utils.Map<Utils.Map<string>> = {};

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
                issues.push({ 'Well-formedness': `Fault handler ${handler.source} -> ${handler.target} increases capabilities` });
            else if (!Utils.setContains(reqs[handler.source], reqs[handler.target]))
                issues.push({ 'Well-formedness': `Fault handler ${handler.source} -> ${handler.target} increases requirements` });
            else if (Utils.setEquals(reqs[handler.source], reqs[handler.target]))
                issues.push({ 'Well-formedness': `Fault handler ${handler.source} -> ${handler.target} preserves requirements` });
            else
                reachable[handler.source][handler.target] = true;
        });

        try {
            handlerReachability(reachable);
        } catch (e) {
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
                        issues.push({ 'Race freedom': `Fault handlers ${s} -> ${s1} -> ${s2} are not transitive` });

        // Check outgoing handlers
        for (var s in edges)
            for (var s1 in edges[s])
                for (var s2 in edges[s]) {
                    if (s1 == s2)
                        continue;

                    if (Utils.setEquals(reqs[s1], reqs[s2]))
                        issues.push({ 'Determinism': `Fault handlers ${s} -> ${s1}/${s2} are not deterministic` });
                    if (!edges[s1][s2] && Utils.setContains(reqs[s1], reqs[s2]))
                        issues.push({ 'Race freedom': `Fault handlers ${s} -> ${s1} -?> ${s2} are not co-transitive` });
                    var intersection = Utils.setIntersection(reqs[s1], reqs[s2]);
                    var union = Utils.setUnion(reqs[s1], reqs[s2]);
                    var foundIntersection = false;
                    var foundUnion = false;
                    for (var s3 in edges[s]) {
                        foundUnion = foundUnion || Utils.setContains(reqs[s3], union);
                        foundIntersection = foundIntersection || Utils.setContains(intersection, reqs[s3]);
                    }
                    if (!foundUnion)
                        issues.push({ 'Race freedom': `Nondeterministic fault handlers ${s} -> ${s1}|${s2} (missing union)` });
                    if (!foundIntersection)
                        issues.push({ 'Race freedom': `Nondeterministic fault handlers ${s} -> ${s1}|${s2} (missing intersection)` });
                }

        for (var s in edges)
            for (var t in edges[s])
                for (var r in Utils.setDiff(reqs[s], reqs[t]))
                    if (!handleReq[s][r] || Utils.setContains(reqs[t], reqs[handleReq[s][r]]))
                        handleReq[s][r] = t;

        return handleReq;
    }

    function nodeTemplateToNode(nodeTemplate: Element, types: Utils.Map<Element>, sharedIssues: any[]) {
        var capNames = toscaMap(nodeTemplate, "Capability", "name");
        var reqNames = toscaMap(nodeTemplate, "Requirement", "name");
        var typeName = nodeTemplate.getAttribute("type").split(':')[1]
        var mProt = new ManagementProtocol.ManagementProtocol(types[typeName]);
        var initialState = mProt.getInitialState();

        var issues = [];

        var states: Utils.Map<Analysis.State> = {};
        var nodeOps: Utils.Set = {};
        var protStates = mProt.getStates();
        var handlers = computeFaultHandlers(protStates, mProt.getFaultHandlers(), issues);
        for (var s in protStates) {
            var state = protStates[s];
            var caps = mapSet(state.getCaps(), capNames.data);
            var reqs = mapSet(state.getReqs(), reqNames.data);
            var trans = mProt.getOutgoingTransitions(s);
            var ops: Utils.Map<Analysis.Operation> = {};
            for (var j = 0; j < trans.length; j++) {
                var opName = trans[j].iface + ":" + trans[j].operation;
                nodeOps[opName] = true;
                var opReqs = mapSet(trans[j].reqs, reqNames.data)
                var prevOp = ops[opName];
                if (prevOp) {
                    if (prevOp.to != trans[j].target) {
                        issues.push({ 'Determinism': `Nondeterministic operation ${s} -[${opName}]-> ${trans[j].target} / ${prevOp.to}` });
                    } else {
                        prevOp.reqs.push(opReqs);
                    }
                } else {
                    ops[opName] = new Analysis.Operation(trans[j].target, [opReqs]);
                }
            }
            var isAlive = s != initialState;
            states[s] = new Analysis.State(isAlive, caps, reqs, ops, mapKeys(handlers[s] || {}, reqNames.data));
        }

        sharedIssues.push(...issues);

        return new UIData(new Analysis.Node(
            initialState,
            typeName,
            mapSet(mProt.getCaps(), capNames.data),
            mapSet(mProt.getReqs(), reqNames.data),
            nodeOps,
            states,
            issues.length === 0 ? initialState : null),
            mergeNames(reqNames.uiNames, capNames.uiNames));
    }

    export function serviceTemplateToApplication(serviceTemplate: Element, types: Utils.Map<Element>, withHardReset: boolean) {
        var nodeTemplates = TOSCA.getToscaElements(serviceTemplate, "NodeTemplate");
        var relationships = TOSCA.getToscaElements(serviceTemplate, "RelationshipTemplate");

        var issues = [];

        var reqNodeId: Utils.Map<string> = {};
        var capNodeId: Utils.Map<string> = {};
        var containedBy: Utils.Map<string> = {};

        var nodes: Utils.Map<Analysis.Node> = {};
        var binding: Utils.Map<string> = {};
        var uiNames: UINames = {};

        for (var i = 0; i < nodeTemplates.length; i++) {
            var template = <HTMLElement>nodeTemplates[i];
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
            var rel = <Element>relationships[i];
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

    export function uiApplicationToElement(app: UIData<Analysis.Application>) {
        var setToList = function (x: Utils.Set) {
            var list = Object.keys(x);

            if (list.length == 0)
                return "-";
            else
                return list.map(function (s) {
                    return app.uiNames[s] || s;
                }).join("<br>");
        }

        var r = ""
        for (var n in app.data.nodes) {
            var node = app.data.nodes[n];
            // Create a new row for the current node
            r += "<tr class='active row-" + node.type + "'>";
            r += "<td>" + app.uiNames[n] + "</td>"
            r += "<td>" + node.type + "</td>"
            r += "<td>" + setToList(node.caps) + "</td>"
            r += "<td>" + setToList(node.reqs) + "</td>"
            r += "<td>" + setToList(node.ops) + "</td>"
            r += "</tr>"
        }

        return r;
    }
}
