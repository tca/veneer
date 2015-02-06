function Var(c) { this.c = c }
function mkvar(c) { return new Var(c); } 
function varp(x) { return (x instanceof Var); }
function vareq(x1, x2) { return x1.c == x2.c };
 
function walk(u, s) {
    var pr = varp(u) && assp(function(v) { return vareq(u, v); }, s);
    return pr ? walk(pr.cdr, s) : u;
}
 
function ext_s(x, v, s) {
    return cons(cons(x, v), s);
}
 
function eqeq(u, v) {
    return function(s_c) {
        var s = unify(u, v, s_c.car);
        return s ? unit(cons(s, s_c.cdr)) : mzero;
    }
}
 
function unit(s_c) { return cons(s_c, mzero); }
var mzero = null;
 
function unify(u, v, s) {
    var u = walk(u, s);
    var v = walk(v, s);
    if (varp(u) && varp(v) && vareq) { return s; }
    else if (varp(u)) { return ext_s(u, v, s); }
    else if (varp(v)) { return ext_s(v, u ,s); }
    else if (pairp(u) && pairp(v)) {
        var s = unify(u.car, v.car, s);
        return s && unify(u.cdr, v.cdr, s);
    } else {
        return (u == v) && s;
    }
}
 
function call_fresh(f) {
    return function(s_c) {
        var c = s_c.cdr;
        return f(mkvar(c))(cons(s_c.car, (c + 1)));
    }
}
function disj(g1, g2) {
    return function(s_c) { return mplus(g1(s_c), g2(s_c)); }
}
function conj(g1, g2) {
    return function(s_c) { return bind(g1(s_c), g2); }
}
 
function mplus($1, $2) {
    if ($1 == null) {
        return $2;
    } else if (procedurep($1)) {
        return function() { return mplus($2, $1()); };
    } else {
        return cons($1.car, mplus($1.cdr, $2));
    }
}
 
function bind($, g) {
    if ($ == null) {
        return mzero;
    } else if (procedurep($)) {
        return function() { return bind($(), g); };
    } else {
        return mplus(g($.car), bind($.cdr, g));
    }
}

function pull($) {
    return procedurep($) ? pull($()) : $;
}

function take(n, $) {
    if (n <= 0) {
        return null;
    } else {
        var $ = pull($);
        return ($ == null) ? null : cons($.car, take(n - 1, $.cdr));
    }
}
