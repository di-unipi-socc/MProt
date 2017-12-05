var Utils;
(function (Utils) {
    function cloneMap(x) {
        var r = {};
        for (var k in x)
            r[k] = x[k];
        return r;
    }
    Utils.cloneMap = cloneMap;
    function makeSet(x) {
        var r = {};
        for (var i = 0; i < x.length; i++)
            r[x[i]] = true;
        return r;
    }
    Utils.makeSet = makeSet;
    function isEmptySet(x) {
        for (var a in x)
            return false;
        return true;
    }
    Utils.isEmptySet = isEmptySet;
    function setCount(x) {
        var r = 0;
        for (var a in x)
            r++;
        return r;
    }
    Utils.setCount = setCount;
    function setContains(a, b) {
        for (var x in b)
            if (!(x in a))
                return false;
        return true;
    }
    Utils.setContains = setContains;
    function setEquals(a, b) {
        return setContains(a, b) && setContains(b, a);
    }
    Utils.setEquals = setEquals;
    function setUnion(a, b) {
        var r = {};
        for (var x in a)
            r[x] = true;
        for (var x in b)
            r[x] = true;
        return r;
    }
    Utils.setUnion = setUnion;
    function setIntersection(a, b) {
        var r = {};
        for (var x in a)
            if (x in b)
                r[x] = true;
        return r;
    }
    Utils.setIntersection = setIntersection;
    function setDiff(a, b) {
        var r = {};
        for (var x in a)
            if (!(x in b))
                r[x] = true;
        return r;
    }
    Utils.setDiff = setDiff;
})(Utils || (Utils = {}));
