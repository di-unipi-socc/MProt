/// <reference path="TOSCA.ts" />
/// <reference path="Utils.ts" />
var __extends = (this && this.__extends) || (function () {
    var extendStatics = Object.setPrototypeOf ||
        ({ __proto__: [] } instanceof Array && function (d, b) { d.__proto__ = b; }) ||
        function (d, b) { for (var p in b) if (b.hasOwnProperty(p)) d[p] = b[p]; };
    return function (d, b) {
        extendStatics(d, b);
        function __() { this.constructor = d; }
        d.prototype = b === null ? Object.create(b) : (__.prototype = b.prototype, new __());
    };
})();
var ManagementProtocol;
(function (ManagementProtocol_1) {
    var mprotNS = "http://di.unipi.it/~soldani/mprot";
    function createElementGroup(els, doc, groupTag, elementTag, attr) {
        var group = doc.createElementNS(mprotNS, groupTag);
        for (var i = 0; i < els.length; i++) {
            var el = doc.createElementNS(mprotNS, elementTag);
            el.setAttribute(attr, els[i]);
            group.appendChild(el);
        }
        return group;
    }
    function attrsToStrings(nodes, attr) {
        var r = {};
        for (var i = 0; i < nodes.length; i++) {
            var el = nodes[i];
            r[el.getAttribute(attr)] = true;
        }
        return r;
    }
    function removeAll(nodes) {
        for (var i = 0; i < nodes.length; i++)
            nodes[i].parentNode.removeChild(nodes[i]);
    }
    function getMProtElements(node, tagName) {
        return node.getElementsByTagNameNS(mprotNS, tagName);
    }
    ManagementProtocol_1.getMProtElements = getMProtElements;
    var State = /** @class */ (function () {
        function State(state, mprot) {
            this.state = state;
            this.mprot = mprot;
        }
        State.prototype.get = function (tagName) {
            return getMProtElements(this.state, tagName);
        };
        State.prototype.getReqs = function () {
            return attrsToStrings(this.get("Requirement"), "name");
        };
        State.prototype.getCaps = function () {
            return attrsToStrings(this.get("Capability"), "name");
        };
        State.prototype.setReqs = function (reqs) {
            removeAll(this.get("ReliesOn"));
            var l = Object.keys(reqs);
            if (l.length != 0)
                this.state.insertBefore(createElementGroup(l, this.state.ownerDocument, "ReliesOn", "Requirement", "name"), this.state.firstChild);
        };
        State.prototype.setCaps = function (caps) {
            removeAll(this.get("Offers"));
            var l = Object.keys(caps);
            if (l.length != 0)
                this.state.appendChild(createElementGroup(l, this.state.ownerDocument, "Offers", "Capability", "name"));
        };
        return State;
    }());
    ManagementProtocol_1.State = State;
    var ManagementProtocol = /** @class */ (function () {
        function ManagementProtocol(nodeType) {
            this.nodeType = nodeType;
            if (nodeType)
                this.reset(nodeType);
        }
        ManagementProtocol.prototype.reset = function (nodeType) {
            this.nodeType = nodeType;
            var mprots = this.getMProt("ManagementProtocol");
            if (mprots.length != 1) {
                removeAll(this.getMProt("ManagementProtocol"));
                this.mprot = nodeType.ownerDocument.createElementNS(mprotNS, "ManagementProtocol");
                nodeType.appendChild(this.mprot);
            }
            else {
                this.mprot = mprots[0];
            }
            var transitions = this.getMProt("Transitions");
            if (transitions.length != 1) {
                removeAll(transitions);
                this.mprot.appendChild(nodeType.ownerDocument.createElementNS(mprotNS, "Transitions"));
            }
            var faultHandlers = this.getMProt("FaultHandlers");
            if (faultHandlers.length != 1) {
                removeAll(faultHandlers);
                this.mprot.appendChild(nodeType.ownerDocument.createElementNS(mprotNS, "FaultHandlers"));
            }
            var initialStates = this.getMProt("InitialState");
            if (initialStates.length != 1)
                this.setInitialState(Object.keys(this.getStates())[0]);
        };
        ManagementProtocol.prototype.getTosca = function (tagName) {
            return TOSCA.getToscaElements(this.nodeType, tagName);
        };
        ManagementProtocol.prototype.getMProt = function (tagName) {
            return getMProtElements(this.nodeType, tagName);
        };
        ManagementProtocol.prototype.getReqs = function () {
            return attrsToStrings(this.getTosca("RequirementDefinition"), "name");
        };
        ManagementProtocol.prototype.getCaps = function () {
            return attrsToStrings(this.getTosca("CapabilityDefinition"), "name");
        };
        ManagementProtocol.prototype.getStates = function () {
            var r = {};
            var states = this.getTosca("InstanceState");
            for (var i = 0; i < states.length; i++) {
                var el = states[i];
                r[el.getAttribute("state")] = new State(el, this);
            }
            return r;
        };
        ManagementProtocol.prototype.addState = function (state) {
            if (this.getStates()[state])
                throw "State already existing";
            var s = this.nodeType.ownerDocument.createElementNS(TOSCA.toscaNS, "InstanceState");
            s.setAttribute("state", state);
            this.getTosca("InstanceStates")[0].appendChild(s);
        };
        ManagementProtocol.prototype.getOps = function () {
            var r = [];
            var ops = this.getTosca("Operation");
            for (var i = 0; i < ops.length; i++) {
                var op = ops[i];
                var iface = op.parentNode;
                r.push({
                    operation: op.getAttribute("name"),
                    iface: iface.getAttribute("name")
                });
            }
            return r;
        };
        ManagementProtocol.prototype.addOp = function (iface, operation) {
            if (this.getOps().filter(function (o) { return o.iface == iface && o.operation == operation; }).length != 0)
                throw "Operation already existing";
            var ifaceEl = null;
            var ifaces = this.getTosca("Interface");
            for (var i = 0; i < ifaces.length; i++)
                if (ifaces[i].getAttribute("name") == iface)
                    ifaceEl = ifaces[i];
            if (ifaceEl == null) {
                ifaceEl = this.nodeType.ownerDocument.createElementNS(TOSCA.toscaNS, "Interface");
                ifaceEl.setAttribute("name", iface);
                this.getTosca("Interfaces")[0].appendChild(ifaceEl);
            }
            var op = this.nodeType.ownerDocument.createElementNS(TOSCA.toscaNS, "Operation");
            op.setAttribute("name", operation);
            ifaceEl.appendChild(op);
        };
        ManagementProtocol.prototype.getInitialState = function () {
            var state = this.getMProt("InitialState")[0];
            return state.getAttribute("state");
        };
        ManagementProtocol.prototype.setInitialState = function (state) {
            removeAll(this.getMProt("InitialState"));
            var stateNode = this.nodeType.ownerDocument.createElementNS(mprotNS, "InitialState");
            stateNode.setAttribute("state", state);
            this.mprot.insertBefore(stateNode, this.mprot.firstChild);
        };
        ManagementProtocol.prototype.findTransition = function (newT) {
            var trans = this.getMProt("Transition");
            for (var i = 0; i < trans.length; i++) {
                var t = trans[i];
                if (t.getAttribute("sourceState") == newT.source &&
                    t.getAttribute("targetState") == newT.target &&
                    t.getAttribute("interfaceName") == newT.iface &&
                    t.getAttribute("operationName") == newT.operation &&
                    Utils.setEquals(attrsToStrings(getMProtElements(t, "Requirement"), "name"), newT.reqs)) {
                    return t;
                }
            }
            return null;
        };
        ManagementProtocol.prototype.addTransition = function (newT) {
            if (this.findTransition(newT))
                throw "Transition already in protocol";
            var t = this.nodeType.ownerDocument.createElementNS(mprotNS, "Transition");
            t.setAttribute("sourceState", newT.source);
            t.setAttribute("targetState", newT.target);
            t.setAttribute("operationName", newT.operation);
            t.setAttribute("interfaceName", newT.iface);
            var reqList = Object.keys(newT.reqs);
            if (reqList.length > 0)
                t.appendChild(createElementGroup(reqList, this.nodeType.ownerDocument, "ReliesOn", "Requirement", "name"));
            this.getMProt("Transitions")[0].appendChild(t);
        };
        ManagementProtocol.prototype.removeTransition = function (trans) {
            var t = this.findTransition(trans);
            t.parentNode.removeChild(t);
        };
        ManagementProtocol.prototype.getTransitions = function () {
            var r = [];
            var trans = this.getMProt("Transition");
            for (var i = 0; i < trans.length; i++) {
                var t = trans[i];
                r.push({
                    source: t.getAttribute("sourceState"),
                    target: t.getAttribute("targetState"),
                    operation: t.getAttribute("operationName"),
                    iface: t.getAttribute("interfaceName"),
                    reqs: attrsToStrings(getMProtElements(t, "Requirement"), "name")
                });
            }
            return r;
        };
        // Returns the set of "state"'s outgoing transitions
        ManagementProtocol.prototype.getOutgoingTransitions = function (state) {
            return this.getTransitions().filter(function (t) { return t.source == state; });
        };
        ManagementProtocol.prototype.findFaultHandler = function (h) {
            var faults = this.getMProt("FaultHandler");
            for (var i = 0; i < faults.length; i++) {
                var t = faults[i];
                if (t.getAttribute("sourceState") == h.source &&
                    t.getAttribute("targetState") == h.target) {
                    return t;
                }
            }
            return null;
        };
        ManagementProtocol.prototype.addFaultHandler = function (h) {
            if (this.findFaultHandler(h))
                throw "Fault handler already in protocol";
            var t = this.nodeType.ownerDocument.createElementNS(mprotNS, "FaultHandler");
            t.setAttribute("sourceState", h.source);
            t.setAttribute("targetState", h.target);
            this.getMProt("FaultHandlers")[0].appendChild(t);
        };
        ManagementProtocol.prototype.removeFaultHandler = function (h) {
            var t = this.findFaultHandler(h);
            t.parentNode.removeChild(t);
        };
        ManagementProtocol.prototype.getFaultHandlers = function () {
            var r = [];
            var trans = this.getMProt("FaultHandler");
            for (var i = 0; i < trans.length; i++) {
                var t = trans[i];
                r.push({
                    source: t.getAttribute("sourceState"),
                    target: t.getAttribute("targetState")
                });
            }
            return r;
        };
        ManagementProtocol.prototype.addDefaultHandling = function (target) {
            var states = this.getStates();
            if (!Utils.isEmptySet(states[target].getReqs()))
                throw "Illegal target state; must have empty requirements";
            var alreadyHandledToEmpty = {};
            this.getFaultHandlers().forEach(function (handler) {
                if (Utils.isEmptySet(states[handler.target].getReqs()))
                    alreadyHandledToEmpty[handler.source] = true;
            });
            for (var source in states)
                if (!Utils.isEmptySet(states[source].getReqs()) &&
                    !alreadyHandledToEmpty[source])
                    this.addFaultHandler({ source: source, target: target });
        };
        ManagementProtocol.prototype.addCrashOps = function (target, iface, operation) {
            var states = this.getStates();
            if (!Utils.isEmptySet(states[target].getReqs()))
                throw "Illegal target state; must have empty requirements";
            for (var source in states)
                if (source != target)
                    this.addTransition({
                        source: source,
                        target: target,
                        iface: iface,
                        operation: operation,
                        reqs: {}
                    });
        };
        ManagementProtocol.prototype.addHardReset = function () {
            throw "TODO";
        };
        return ManagementProtocol;
    }());
    ManagementProtocol_1.ManagementProtocol = ManagementProtocol;
    var ManagementProtocolEditor = /** @class */ (function (_super) {
        __extends(ManagementProtocolEditor, _super);
        function ManagementProtocolEditor(doc, name, onend) {
            var _this = _super.call(this, null) || this;
            _this.doc = doc;
            var that = _this;
            var findNodeType = function () {
                var nts = doc.get("NodeType");
                for (var i = 0; i < nts.length; i++) {
                    var nt = nts[i];
                    if (nt.getAttribute("name") == name)
                        return nt;
                }
                throw "Did not find NodeType " + name;
            };
            var init = function () {
                var defs = doc.doc.firstChild;
                defs.setAttribute("xmlns:mprot", mprotNS);
                that.save(function () {
                    doc.reload(function () {
                        that.reset(findNodeType());
                        if (onend)
                            onend();
                    });
                });
            };
            _this.reset(findNodeType());
            if (!_this.mprot)
                init();
            else if (onend)
                onend();
            return _this;
        }
        ManagementProtocolEditor.prototype.save = function (onend) {
            this.doc.save(onend);
        };
        ManagementProtocolEditor.prototype.getXML = function () {
            return this.doc.getXML();
        };
        return ManagementProtocolEditor;
    }(ManagementProtocol));
    ManagementProtocol_1.ManagementProtocolEditor = ManagementProtocolEditor;
})(ManagementProtocol || (ManagementProtocol = {}));
