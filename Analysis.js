/// <reference path="Utils.ts" />
var Analysis;
(function (Analysis) {
    var Step = /** @class */ (function () {
        function Step(nodeId, opId, isOp) {
            this.nodeId = nodeId;
            this.opId = opId;
            this.isOp = isOp;
        }
        return Step;
    }());
    Analysis.Step = Step;
    // An operation can only go to a single state,
    // it might be possible to perform it with multiple sets of constraints are allowed
    var Operation = /** @class */ (function () {
        function Operation(to, reqs) {
            this.to = to;
            this.reqs = reqs;
        }
        return Operation;
    }());
    Analysis.Operation = Operation;
    var State = /** @class */ (function () {
        function State(isAlive, caps, reqs, ops, handlers) {
            this.isAlive = isAlive;
            this.caps = caps;
            this.reqs = reqs;
            this.ops = ops;
            this.handlers = handlers;
        }
        return State;
    }());
    Analysis.State = State;
    var Node = /** @class */ (function () {
        function Node(initialState, type, caps, reqs, ops, states, stateId) {
            this.initialState = initialState;
            this.type = type;
            this.caps = caps;
            this.reqs = reqs;
            this.ops = ops;
            this.states = states;
            this.stateId = stateId;
            // Check input states
            for (var sid in states) {
                var state = states[sid];
                for (var c in state.caps)
                    if (!caps[c])
                        throw "Unknown capability " + c + " in state " + sid;
                for (var r in state.reqs)
                    if (!reqs[r])
                        throw "Unknown requirement " + r + " in state " + sid;
                for (var o in state.ops) {
                    if (!ops[o])
                        throw "Unknown operation " + o + " in state " + sid;
                    if (!state.ops[o].to)
                        throw "Unknown destination state " + state.ops[o].to + " in transition " + o + " from state " + sid;
                    for (var i = 0; i < state.ops[o].reqs.length; i++)
                        for (var r in state.ops[o].reqs[i])
                            if (!reqs[r])
                                throw "Unknown requirement " + r + " in transition " + o + " from state " + sid;
                }
                for (var r in state.handlers) {
                    if (!reqs[r])
                        throw "Unknown requirement " + r + " in fault handler from state " + sid;
                    if (!states[state.handlers[r]])
                        throw "Unknown target state " + state.handlers[r] + " in handler of " + r + " from state " + sid;
                }
            }
            if (this.stateId)
                this.state = this.states[this.stateId];
        }
        Node.prototype.performOp = function (opId) {
            if (!(opId in this.state.ops))
                throw "Operation " + opId + " is not supported in the current state";
            return new Node(this.initialState, this.type, this.caps, this.reqs, this.ops, this.states, this.state.ops[opId].to);
        };
        Node.prototype.handleFault = function (req) {
            if (!(req in this.state.handlers))
                throw "No fault handler for " + req + " in the current state";
            return new Node(this.initialState, this.type, this.caps, this.reqs, this.ops, this.states, this.state.handlers[req]);
        };
        Node.prototype.doHardReset = function () {
            return new Node(this.initialState, this.type, this.caps, this.reqs, this.ops, this.states, this.initialState);
        };
        return Node;
    }());
    Analysis.Node = Node;
    var Application = /** @class */ (function () {
        function Application(nodes, binding, containedBy, hasHardReset) {
            this.nodes = nodes;
            this.binding = binding;
            this.containedBy = containedBy;
            this.hasHardReset = hasHardReset;
            this.reqNodeId = {};
            this.capNodeId = {};
            this.reqs = {};
            this.caps = {};
            this.faults = {};
            this.isConsistent = true;
            this.isContainmentConsistent = true;
            this.canRun = true;
            var states = [];
            for (var nodeId in nodes) {
                var node = nodes[nodeId];
                var nodeState = node.state;
                states.push(nodeId + "=" + node.stateId);
                if (nodeState) {
                    this.reqs = Utils.setUnion(this.reqs, nodeState.reqs);
                    this.caps = Utils.setUnion(this.caps, nodeState.caps);
                    if (nodeState.isAlive && (nodeId in containedBy))
                        this.isContainmentConsistent = this.isContainmentConsistent && nodes[containedBy[nodeId]].state.isAlive;
                }
                else {
                    this.canRun = false;
                }
                for (var r in node.reqs)
                    this.reqNodeId[r] = nodeId;
                for (var c in node.caps)
                    this.capNodeId[c] = nodeId;
            }
            for (var req in this.reqs)
                if (!this.isReqSatisfied(req))
                    this.faults[req] = true;
            this.isConsistent = Utils.isEmptySet(this.faults);
            this.globalState = states.sort().join("|");
        }
        Application.prototype.isReqSatisfied = function (req) {
            return this.caps[this.binding[req]] || false;
        };
        Application.prototype.areReqsSatisfied = function (reqs) {
            for (var req in reqs)
                if (!this.isReqSatisfied(req))
                    return false;
            return true;
        };
        Application.prototype.unsatisfiedOpConstraints = function (nodeId, opId) {
            if (!this.isConsistent)
                return "Operations are not allowed while faults are pending";
            if (this.hasHardReset && !this.isContainmentConsistent)
                return "Operations are not allowed while a liveness constraint is failing";
            if (!(nodeId in this.nodes))
                return "There is no " + nodeId + " node in the application";
            if (!(opId in this.nodes[nodeId].state.ops))
                return "The " + opId + " operation is not available in the current state of the " + nodeId + " node";
            var opReqSets = this.nodes[nodeId].state.ops[opId].reqs;
            for (var i = 0; i < opReqSets.length; i++)
                if (this.areReqsSatisfied(opReqSets[i]))
                    return "";
            return "The requirements of the operation cannot be satisfied";
        };
        Application.prototype.canPerformOp = function (nodeId, opId) {
            return !this.unsatisfiedOpConstraints(nodeId, opId);
        };
        Application.prototype.performOp = function (nodeId, opId) {
            var constraints = this.unsatisfiedOpConstraints(nodeId, opId);
            if (constraints)
                throw constraints;
            var nodes = Utils.cloneMap(this.nodes);
            var node = nodes[nodeId];
            nodes[nodeId] = node.performOp(opId);
            return new Application(nodes, this.binding, this.containedBy, this.hasHardReset);
        };
        Application.prototype.unsatisfiedHandlerConstraints = function (nodeId, r) {
            if (!(r in this.faults))
                return "Requirement " + r + " is not currently faulted";
            if (!(nodeId in this.nodes))
                return "There is no " + nodeId + " node in the application";
            if (!(r in this.nodes[nodeId].state.handlers))
                return "The " + r + " requirement has no fault handler from the current state of the " + nodeId + " node";
        };
        Application.prototype.canHandleFault = function (nodeId, r) {
            return !this.unsatisfiedHandlerConstraints(nodeId, r);
        };
        Application.prototype.handleFault = function (nodeId, r) {
            var constraints = this.unsatisfiedHandlerConstraints(nodeId, r);
            if (constraints)
                throw constraints;
            var nodes = Utils.cloneMap(this.nodes);
            var node = nodes[nodeId];
            nodes[nodeId] = node.handleFault(r);
            return new Application(nodes, this.binding, this.containedBy, this.hasHardReset);
        };
        Application.prototype.unsatisfiedHardResetConstraints = function (nodeId) {
            if (!this.hasHardReset)
                return "Hard resets are not enabled on the application";
            if (!(nodeId in this.containedBy))
                return "The node " + nodeId + "is not contained in another node";
            var container = this.containedBy[nodeId];
            if (this.nodes[container].state.isAlive)
                return container + " (the container of " + nodeId + ") is alive";
        };
        Application.prototype.canHardReset = function (nodeId) {
            return !this.unsatisfiedHardResetConstraints(nodeId);
        };
        Application.prototype.doHardReset = function (nodeId) {
            var constraints = this.unsatisfiedHardResetConstraints(nodeId);
            if (constraints)
                throw constraints;
            var nodes = Utils.cloneMap(this.nodes);
            var node = nodes[nodeId];
            nodes[nodeId] = node.doHardReset();
            return new Application(nodes, this.binding, this.containedBy, this.hasHardReset);
        };
        return Application;
    }());
    Analysis.Application = Application;
    function reachable(application) {
        var visited = {};
        var visit = function (app) {
            if (app.globalState in visited)
                return;
            visited[app.globalState] = app;
            for (var nodeId in app.nodes)
                for (var opId in app.nodes[nodeId].ops)
                    if (app.canPerformOp(nodeId, opId))
                        visit(app.performOp(nodeId, opId));
            for (var nodeId in app.nodes)
                for (var req in app.nodes[nodeId].reqs)
                    if (app.canHandleFault(nodeId, req))
                        visit(app.handleFault(nodeId, req));
            for (var nodeId in app.nodes)
                if (app.canHardReset(nodeId))
                    visit(app.doHardReset(nodeId));
        };
        visit(application);
        return visited;
    }
    Analysis.reachable = reachable;
    function plans(app) {
        var stateData = reachable(app);
        var states = Object.keys(stateData);
        var stateIdx = {};
        for (var i = 0; i < states.length; i++) {
            stateIdx[states[i]] = i;
        }
        var costs = states.map(function (_, i) { return states.map(function (_, j) { return i === j ? 0 : NaN; }); });
        var steps = states.map(function (_, i) { return states.map(function (_, j) { return undefined; }); });
        for (var src = 0; src < states.length; src++) {
            var state = stateData[states[src]];
            for (var nodeId in state.nodes)
                for (var opId in state.nodes[nodeId].ops)
                    if (state.canPerformOp(nodeId, opId)) {
                        var dst = stateIdx[state.performOp(nodeId, opId).globalState];
                        var newCost = 1; // TODO: we might want to compute the cost in a clever way
                        // ! used to abuse NaN comparison (which always compares as false)
                        if (!(costs[src][dst] <= newCost)) {
                            costs[src][dst] = newCost;
                            steps[src][dst] = new Step(nodeId, opId, true);
                        }
                    }
            for (var nodeId in state.nodes)
                for (var req in state.nodes[nodeId].reqs)
                    if (state.canHandleFault(nodeId, req)) {
                        var dst = stateIdx[state.handleFault(nodeId, req).globalState];
                        var newCost = 1; // TODO: we might want to compute the cost in a clever way
                        // ! used to abuse NaN comparison (which always compares as false)
                        if (!(costs[src][dst] <= newCost)) {
                            costs[src][dst] = newCost;
                            steps[src][dst] = new Step(nodeId, req, false);
                        }
                    }
            for (var nodeId in state.nodes)
                if (state.canHardReset(nodeId)) {
                    var dst = stateIdx[state.doHardReset(nodeId).globalState];
                    var newCost = 1; // TODO: we might want to compute the cost in a clever way
                    // ! used to abuse NaN comparison (which always compares as false)
                    if (!(costs[src][dst] <= newCost)) {
                        costs[src][dst] = newCost;
                        steps[src][dst] = new Step(nodeId, null, false);
                    }
                }
        }
        for (var via = 0; via < states.length; via++) {
            for (var src = 0; src < states.length; src++) {
                if (src == via || isNaN(costs[src][via]))
                    continue;
                for (var dst = 0; dst < states.length; dst++) {
                    // ! used to abuse NaN comparison (which always compares as false)
                    var newCost = costs[src][via] + costs[via][dst];
                    if (!isNaN(newCost) && !(costs[src][dst] <= newCost)) {
                        costs[src][dst] = newCost;
                        steps[src][dst] = steps[src][via];
                    }
                }
            }
        }
        var costsMap = {};
        var stepsMap = {};
        for (var src = 0; src < states.length; src++) {
            var costSrcMap = {};
            var stepSrcMap = {};
            for (var dst = 0; dst < states.length; dst++) {
                if (!isNaN(costs[src][dst])) {
                    var dstString = states[dst];
                    costSrcMap[dstString] = costs[src][dst];
                    stepSrcMap[dstString] = steps[src][dst];
                }
            }
            var srcString = states[src];
            costsMap[srcString] = costSrcMap;
            stepsMap[srcString] = stepSrcMap;
        }
        return { costs: costsMap, steps: stepsMap };
    }
    Analysis.plans = plans;
})(Analysis || (Analysis = {}));
