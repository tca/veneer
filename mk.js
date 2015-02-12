function Var(c) { this.c = c }
function mkvar(c) { return new Var(c); } 
function varp(x) { return (x instanceof Var); }
function vareq(x1, x2) { return x1.c == x2.c };

function MiniKanrenState(s, c, d, sy) {
    this.substitution = s;
    this.counter = c;
    this.diseq = d;
    this.symbols = sy;
}
function Mks(s, c, d, sy) { return new MiniKanrenState(s,c,d,sy); }

function walk(u, s) {
    var pr;
    while(true) {
        pr = varp(u) && assp(function(v) { return vareq(u, v); }, s);
        if(pr != false) {
            u = pr.cdr;
        } else {
            return u;
        }
    }
}

function occurs_check(x, v, s) {
    var v = walk(v, s);
    if(varp(v)) {
        return vareq(v, x);
    } else if (pairp(v)) {
        return occurs_check(x, v.car, s) || occurs_check(x, v.cdr, s);
    } else {
        return false;
    }
}
 
function ext_s_check(x, v, s) {
    return occurs_check(x, v, s) ? false : cons(cons(x, v), s);
}
 
function eqeq(u, v) {
    return function(mks) {
        var s = unify(u, v, mks.substitution);
        return s != false ? normalize_disequality_store(Mks(s, mks.counter, mks.diseq, mks.symbols)) : mzero;
    }
}

function noteqeq(u, v) {
    return function(mks) {
        var d = disequality(u, v, mks.substitution);
        return d != false ? unit(Mks(mks.substitution, mks.counter, cons(d,mks.diseq), mks.symbols)) : mzero;
    }
}

function symbolo(s) {
    return function(mks) {
        return normalize_disequality_store(Mks(mks.substitution, mks.counter, mks.diseq, cons(s, mks.symbols)));
    }
}

function unit(mks) { return cons(mks, mzero); }
var mzero = null;
 
function unify(u, v, s) {
    var u = walk(u, s);
    var v = walk(v, s);
    if (varp(u) && varp(v) && vareq(u, v)) { return s; }
    else if (varp(u)) { return ext_s_check(u, v, s); }
    else if (varp(v)) { return ext_s_check(v, u ,s); }
    else if (pairp(u) && pairp(v)) {
        var s = unify(u.car, v.car, s);
        return (s != false) && unify(u.cdr, v.cdr, s);
    } else {
        return (u == v) && s;
    }
}

function subtract_substitution(s_hat, s) {
    // This function requires that s^ is some stuff consed onto s
    if(s_hat === s) { // we use === for pointer equality
        return null;
    }
    else {
        return cons(s_hat.car, subtract_substitution(s_hat.cdr, s));
    }
}

function disequality(u, v, s) {
    var s_hat = unify(u, v, s);
    if(s_hat != false) {
        var d = subtract_substitution(s_hat, s);
        return (d == null) ? false : d;
    }
    else {
        return null;
    }
}

function normalize_disequality_store(mks) {
    var s = mks.substitution;
    var c = mks.counter;
    var d = mks.diseq;
    var dn = null;
    var sy = mks.symbols;
    var syn = null;

    while(sy != null) {
        var i = walk(sy.car, s);
        sy = sy.cdr;
        
        if (varp(i)) {
            syn = cons(i, syn);
        }
        else if(symbolp(i)) {
            continue;
        }
        else {
            return mzero;
        }
    }
    
    while(d != null) {
        var es = d.car;

        if(es != null) {
            d_hat = disequality(map(car, es), map(cdr, es), s);
            
            if(d_hat == false) {
                return mzero;
            }

            dn = cons(d_hat, dn);
        }
        
        d = d.cdr;
    }

    return unit(Mks(s, c, dn, syn));
}
 
function call_fresh(f) {
    return function(mks) {
        var c = mks.counter;
        return f(mkvar(c))(Mks(mks.substitution, (c + 1), mks.diseq, mks.symbols));
    }
}

function disj(g1, g2) {
    return function(mks) { return mplus(g1(mks), g2(mks)); }
}
function conj(g1, g2) {
    return function(mks) { return bind(g1(mks), g2); }
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
    while(procedurep($)) {
        $ = $();
    } return $;
}

function take(n, $) {
    if (n <= 0) {
        return null;
    } else {
        var $ = pull($);
        return ($ == null) ? null : cons($.car, take(n - 1, $.cdr));
    }
}

function take_all($) {
    $ = pull($);
    return ($ == null) ? null : cons($.car, take_all($.cdr));
}

function reify_first(mks) {
    var v = walk_star(mkvar(0), mks.substitution);
    return walk_star(v, reify_s(v, null));
}

function walk_star(v, s) {
    var v1 = walk(v, s);
    if (varp(v1)) {
        return v1;
    } else if (pairp(v1)) {
        return cons(walk_star(v1.car, s),
                    walk_star(v1.cdr, s));
    } else {
        return v1;
    }
}

function reify_s(v, s) {
    var v1 = walk(v, s);
    if (varp(v1)) {
        return cons(cons(v1, reify_name(length(s))), s);
    } else if (pairp(v1)) {
        return reify_s(v1.cdr, reify_s(v1.car, s));
    } else {
        return s;
    }
}

function reify_name(n) {
    return { toString: function() { return ["_", n].join("."); } };
}
