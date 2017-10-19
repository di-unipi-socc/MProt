/// <reference path="Utils.ts" />

module Analysis {
    export class Step {
        constructor(public nodeId: string,
                    public opId: string,
                    public isOp: boolean) { }
    }

    // An operation can only go to a single state,
    // it might be possible to perform it with multiple sets of constraints are allowed
    export class Operation {
        constructor(public to: string,
            public reqs: Utils.Set[]) { }
    }

    export class State {
        constructor(
            public isAlive: boolean,
            public caps: Utils.Set,
            public reqs: Utils.Set,
            public ops: Utils.Map<Operation>,
            public handlers: Utils.Map<string>) { }
    }

    export class Node {
        public state: State;

        constructor(
            public initialState: string,
            public type: string,
            public caps: Utils.Set,
            public reqs: Utils.Set,
            public ops: Utils.Set,
            public states: Utils.Map<State>,
            public stateId: string) {

            // Check input states
            for (const sid in states) {
                const state = states[sid];
                for (const c in state.caps)
                    if (!caps[c])
                        throw "Unknown capability " + c + " in state " + sid;

                for (const r in state.reqs)
                    if (!reqs[r])
                        throw "Unknown requirement " + r + " in state " + sid;

                for (const o in state.ops) {
                    if (!ops[o])
                        throw "Unknown operation " + o + " in state " + sid;

                    if (!state.ops[o].to)
                        throw "Unknown destination state " + state.ops[o].to + " in transition " + o + " from state " + sid;

                    for (let i = 0; i < state.ops[o].reqs.length; i++)
                        for (const r in state.ops[o].reqs[i])
                            if (!reqs[r])
                                throw "Unknown requirement " + r + " in transition " + o + " from state " + sid;
                }

                for (const r in state.handlers) {
                    if (!reqs[r])
                        throw "Unknown requirement " + r + " in fault handler from state " + sid;
                    if (!states[state.handlers[r]])
                        throw "Unknown target state " + state.handlers[r] + " in handler of " + r + " from state " + sid;
                }
            }

            this.state = this.states[this.stateId];
        }

        performOp(opId: string) {
            if (!(opId in this.state.ops))
                throw "Operation " + opId + " is not supported in the current state";

            return new Node(
                this.initialState,
                this.type,
                this.caps,
                this.reqs,
                this.ops,
                this.states,
                this.state.ops[opId].to
            );
        }

        handleFault(req: string) {
            if (!(req in this.state.handlers))
                throw "No fault handler for " + req + " in the current state";

            return new Node(
                this.initialState,
                this.type,
                this.caps,
                this.reqs,
                this.ops,
                this.states,
                this.state.handlers[req]
            );
        }

        doHardReset() {
            return new Node(
                this.initialState,
                this.type,
                this.caps,
                this.reqs,
                this.ops,
                this.states,
                this.initialState
            );
        }
    }

    export class Application {
        public reqNodeId: Utils.Map<string> = {};
        public capNodeId: Utils.Map<string> = {};
        public globalState: string;
        public reqs: Utils.Set = {};
        public caps: Utils.Set = {};
        public faults: Utils.Set = {};
        public isConsistent = true;
        public isContainmentConsistent = true;

        constructor(public nodes: Utils.Map<Node>,
                    public binding: Utils.Map<string>,
                    public containedBy: Utils.Map<string>,
                    public hasHardReset) {
            const states = [];
            for (const nodeId in nodes) {
                const node = nodes[nodeId];
                const nodeState = node.state;
                states.push(nodeId + "=" + node.stateId);
                this.reqs = Utils.setUnion(this.reqs, nodeState.reqs);
                this.caps = Utils.setUnion(this.caps, nodeState.caps);
                if (nodeState.isAlive && (nodeId in containedBy))
                    this.isContainmentConsistent = this.isContainmentConsistent && nodes[containedBy[nodeId]].state.isAlive;

                for (const r in node.reqs)
                    this.reqNodeId[r] = nodeId;
                for (const c in node.caps)
                    this.capNodeId[c] = nodeId;
            }

            for (const req in this.reqs)
                if (!this.isReqSatisfied(req))
                    this.faults[req] = true;

            this.isConsistent = Utils.isEmptySet(this.faults);
            this.globalState = states.sort().join("|");
        }

        private isReqSatisfied(req: string) {
            return this.caps[this.binding[req]] || false;
        }

        private areReqsSatisfied(reqs: Utils.Set) {
            for (const req in reqs)
                if (!this.isReqSatisfied(req))
                    return false;

            return true;
        }

        unsatisfiedOpConstraints(nodeId: string, opId: string) {
            if (!this.isConsistent)
                return "Operations are not allowed while faults are pending";

            if (this.hasHardReset && !this.isContainmentConsistent)
                return "Operations are not allowed while a liveness constraint is failing";

            if (!(nodeId in this.nodes))
                return "There is no " + nodeId + " node in the application";

            if (!(opId in this.nodes[nodeId].state.ops))
                return "The " + opId + " operation is not available in the current state of the " + nodeId + " node";

            const opReqSets = this.nodes[nodeId].state.ops[opId].reqs;
            for (let i = 0; i < opReqSets.length; i++)
                if (this.areReqsSatisfied(opReqSets[i]))
                    return "";

            return "The requirements of the operation cannot be satisfied";
        }

        canPerformOp(nodeId: string, opId: string) {
            return !this.unsatisfiedOpConstraints(nodeId, opId);
        }

        performOp(nodeId: string, opId: string) {
            const constraints = this.unsatisfiedOpConstraints(nodeId, opId);
            if (constraints)
                throw constraints;

            const nodes = Utils.cloneMap(this.nodes);
            const node = nodes[nodeId];
            nodes[nodeId] = node.performOp(opId);
            return new Application(nodes, this.binding, this.containedBy, this.hasHardReset);
        }

        unsatisfiedHandlerConstraints(nodeId: string, r: string) {
            if (!(r in this.faults))
                return "Requirement " + r + " is not currently faulted";

            if (!(nodeId in this.nodes))
                return "There is no " + nodeId + " node in the application";

            if (!(r in this.nodes[nodeId].state.handlers))
                return "The " + r + " requirement has no fault handler from the current state of the " + nodeId + " node";
        }

        canHandleFault(nodeId: string, r: string) {
            return !this.unsatisfiedHandlerConstraints(nodeId, r);
        }

        handleFault(nodeId: string, r: string) {
            const constraints = this.unsatisfiedHandlerConstraints(nodeId, r);
            if (constraints)
                throw constraints;

            const nodes = Utils.cloneMap(this.nodes);
            const node = nodes[nodeId];
            nodes[nodeId] = node.handleFault(r);
            return new Application(nodes, this.binding, this.containedBy, this.hasHardReset);
        }

        unsatisfiedHardResetConstraints(nodeId: string) {
            if (!this.hasHardReset)
                return "Hard resets are not enabled on the application";

            if (!(nodeId in this.containedBy))
                return "The node " + nodeId + "is not contained in another node";

            const container = this.containedBy[nodeId];
            if (this.nodes[container].state.isAlive)
                return container + " (the container of " + nodeId + ") is alive";
        }

        canHardReset(nodeId: string) {
            return !this.unsatisfiedHardResetConstraints(nodeId);
        }

        doHardReset(nodeId: string) {
            const constraints = this.unsatisfiedHardResetConstraints(nodeId);
            if (constraints)
                throw constraints;

            const nodes = Utils.cloneMap(this.nodes);
            const node = nodes[nodeId];
            nodes[nodeId] = node.doHardReset();
            return new Application(nodes, this.binding, this.containedBy, this.hasHardReset);
        }
    }

    export function reachable(application: Application) {
        const visited: Utils.Map<Application> = {};
        const visit = function(app: Application) {
            if (app.globalState in visited)
                return;

            visited[app.globalState] = app;

            for (const nodeId in app.nodes)
                for (const opId in app.nodes[nodeId].ops)
                    if (app.canPerformOp(nodeId, opId))
                        visit(app.performOp(nodeId, opId));

            for (const nodeId in app.nodes)
                for (const req in app.nodes[nodeId].reqs)
                    if (app.canHandleFault(nodeId, req))
                        visit(app.handleFault(nodeId, req));

            for (const nodeId in app.nodes)
                if (app.canHardReset(nodeId))
                    visit(app.doHardReset(nodeId));
        };
        visit(application);
        return visited;
    }

    export function plans(app: Application) {
        const stateData = reachable(app);
        const states = Object.keys(stateData);
        const stateIdx = {};
        for (let i = 0; i < states.length; i++) {
            stateIdx[states[i]] = i;
        }

        const costs = states.map((_, i) => states.map((_, j) => i === j ? 0 : NaN));
        const steps: Step[][] = states.map((_, i) => states.map((_, j) => undefined));

        for (let src = 0; src < states.length; src++) {
            const state = stateData[states[src]];

            for (const nodeId in state.nodes)
                for (const opId in state.nodes[nodeId].ops)
                    if (state.canPerformOp(nodeId, opId)) {
                        const dst = stateIdx[state.performOp(nodeId, opId).globalState];
                        const newCost = 1; // TODO: we might want to compute the cost in a clever way
                        // ! used to abuse NaN comparison (which always compares as false)
                        if (!(costs[src][dst] <= newCost)) {
                            costs[src][dst] = newCost;
                            steps[src][dst] = new Step(nodeId, opId, true);
                        }
                    }

            for (const nodeId in state.nodes)
                for (const req in state.nodes[nodeId].reqs)
                    if (state.canHandleFault(nodeId, req)) {
                        const dst = stateIdx[state.handleFault(nodeId, req).globalState];
                        const newCost = 1; // TODO: we might want to compute the cost in a clever way
                        // ! used to abuse NaN comparison (which always compares as false)
                        if (!(costs[src][dst] <= newCost)) {
                            costs[src][dst] = newCost;
                            steps[src][dst] = new Step(nodeId, req, false);
                        }
                    }

            for (const nodeId in state.nodes)
                if (state.canHardReset(nodeId)) {
                    const dst = stateIdx[state.doHardReset(nodeId).globalState];
                    const newCost = 1; // TODO: we might want to compute the cost in a clever way
                    // ! used to abuse NaN comparison (which always compares as false)
                    if (!(costs[src][dst] <= newCost)) {
                        costs[src][dst] = newCost;
                        steps[src][dst] = new Step(nodeId, null, false);
                    }
                }
        }

        for (let via = 0; via < states.length; via++) {
            for (let src = 0; src < states.length; src++) {
                if (src == via || isNaN(costs[src][via]))
                    continue;

                for (let dst = 0; dst < states.length; dst++) {
                    // ! used to abuse NaN comparison (which always compares as false)
                    const newCost = costs[src][via] + costs[via][dst];
                    if (!isNaN(newCost) && !(costs[src][dst] <= newCost)) {
                        costs[src][dst] = newCost;
                        steps[src][dst] = steps[src][via];
                    }
                }
            }
        }

        const costsMap = {};
        const stepsMap = {};
        for (let src = 0; src < states.length; src++) {
            const costSrcMap = {};
            const stepSrcMap = {};
            for (let dst = 0; dst < states.length; dst++) {
                if (!isNaN(costs[src][dst])) {
                    const dstString = states[dst];
                    costSrcMap[dstString] = costs[src][dst];
                    stepSrcMap[dstString] = steps[src][dst];
                }
            }
            const srcString = states[src];
            costsMap[srcString] = costSrcMap;
            stepsMap[srcString] = stepSrcMap;
        }

        return { costs: costsMap, steps: stepsMap };
    }
}
