/// <reference path="lib/zip-fs.js.d.ts" />
/// <reference path="TOSCA.ts" />
/// <reference path="Utils.ts" />
var Csar;
(function (Csar_1) {
    var Csar = /** @class */ (function () {
        function Csar(blob, onend) {
            this.fs = new zip.fs.FS();
            this.docs = {};
            var that = this;
            var locations = [];
            var relativePath = function (base, location) {
                var pathElements = base.split("/");
                pathElements.pop();
                pathElements = pathElements.concat(location.split("/"));
                var j = 0;
                for (var i = 0; i < pathElements.length; i++) {
                    if (pathElements[i] == "..")
                        j--;
                    else if (pathElements[i] != ".")
                        pathElements[j++] = pathElements[i];
                }
                return pathElements.slice(0, j).join("/");
            };
            var parseToscaDocuments = function () {
                if (locations.length == 0)
                    return onend();
                var fileName = locations.pop();
                var load = function (onend) {
                    var file = that.fs.find(fileName);
                    file.getText(onend);
                };
                var save = function (text, onend) {
                    var file = that.fs.find(fileName);
                    that.fs.remove(file);
                    var pathElements = fileName.split("/");
                    var name = pathElements.pop();
                    var dir = that.fs.find(pathElements.join("/"));
                    dir.addText(name, text);
                    onend();
                };
                var doc;
                var parseDoc = function () {
                    that.docs[fileName] = doc;
                    var imports = doc.get("Import");
                    for (var i = 0; i < imports.length; i++) {
                        var location = imports[i].getAttribute("location");
                        if (!(location in that.docs))
                            locations.push(relativePath(fileName, unescape(location)));
                    }
                    parseToscaDocuments();
                };
                doc = new TOSCA.ToscaDocument(load, save, parseDoc);
            };
            var parseToscaMeta = function (data) {
                that.entryDef = /Entry-Definitions: *(.*)/.exec(data)[1];
                locations.push(that.entryDef);
                parseToscaDocuments();
            };
            var parseCsar = function () {
                var file = that.fs.find("TOSCA-Metadata/TOSCA.meta");
                file.getText(parseToscaMeta);
            };
            this.fs.importBlob(blob, parseCsar);
        }
        Csar.prototype.get = function (name) {
            var r = [];
            for (var d in this.docs) {
                var els = this.docs[d].get(name);
                for (var i = 0; i < els.length; i++) {
                    r.push({ doc: this.docs[d], element: els[i] });
                }
            }
            return r;
        };
        Csar.prototype.getTypes = function () {
            var nodeTypes = this.get("NodeType");
            var types = {};
            for (var i = 0; i < nodeTypes.length; i++) {
                var type = nodeTypes[i].element;
                types[type.getAttribute("name")] = type;
            }
            return types;
        };
        Csar.prototype.getTypeDocuments = function () {
            var nodeTypes = this.get("NodeType");
            var docs = {};
            for (var i = 0; i < nodeTypes.length; i++) {
                var type = nodeTypes[i].element;
                docs[type.getAttribute("name")] = nodeTypes[i].doc;
            }
            return docs;
        };
        Csar.prototype.exportBlob = function (onend) {
            this.fs.exportBlob(onend);
        };
        return Csar;
    }());
    Csar_1.Csar = Csar;
})(Csar || (Csar = {}));
