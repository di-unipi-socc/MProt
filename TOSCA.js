/// <reference path="lib/jquery/jquery.d.ts" />
var TOSCA;
(function (TOSCA) {
    TOSCA.toscaNS = "http://docs.oasis-open.org/tosca/ns/2011/12";
    var ToscaDocument = /** @class */ (function () {
        function ToscaDocument(_load, _save, onend) {
            this._load = _load;
            this._save = _save;
            this.reload(onend);
        }
        ToscaDocument.prototype.get = function (name) {
            return this.doc.getElementsByTagNameNS(TOSCA.toscaNS, name);
        };
        ToscaDocument.prototype.reload = function (onend) {
            var that = this;
            this._load(function (data) {
                that.doc = $.parseXML(data);
                onend();
            });
        };
        ToscaDocument.prototype.getXMLString = function () {
            return new XMLSerializer().serializeToString(this.doc);
        };
        ToscaDocument.prototype.getXML = function () {
            return new Blob([this.getXMLString()], { type: "text/xml" });
        };
        ToscaDocument.prototype.save = function (onend) {
            this._save(this.getXMLString(), onend);
        };
        return ToscaDocument;
    }());
    TOSCA.ToscaDocument = ToscaDocument;
    // Finds an element (of a certain "name") inside "toscaDoc"
    function getToscaElements(toscaDoc, name) {
        return toscaDoc.getElementsByTagNameNS(TOSCA.toscaNS, name);
    }
    TOSCA.getToscaElements = getToscaElements;
})(TOSCA || (TOSCA = {}));
