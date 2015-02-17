function Var(c) { this.c = c; }
function mkvar(c) { return new Var(c); } 
function varp(x) { return (x instanceof Var); }
function vareq(x1, x2) { return x1.c == x2.c };

function MiniKanrenState(s, c, d, sy, nm, ab) {
    this.substitution = s;
    this.counter = c;
    this.diseq = d;
    this.symbols = sy;
    this.numbers = nm;
    this.absentee = ab;
}
function Mks(s, c, d, sy, nm, ab) { return new MiniKanrenState(s,c,d,sy,nm,ab); }

var not_found = [];
function walk(u, s) {
    var pr;
    var v;
    while(true) {
        if (varp(u)) {
            v = s.get(u.c, not_found);
            if (v === not_found) {
                return u;
            } else {
                u = v;
            }
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
    return occurs_check(x, v, s) ? false : s.set(x.c, v);
}
 
function eqeq(u, v) {
    return function(mks) {
        var s = unify(u, v, mks.substitution);
        return s !== false ? normalize_constraint_store(Mks(s, mks.counter, mks.diseq, mks.symbols, mks.numbers, mks.absentee)) : mzero;
    }
}

function noteqeq(u, v) {
    return function(mks) {
        var d = disequality(u, v, mks.substitution);
        return d !== false ? unit(Mks(mks.substitution, mks.counter, cons(d,mks.diseq), mks.symbols, mks.numbers, mks.absentee)) : mzero;
    }
}

function symbolo(s) {
    return function(mks) {
        return normalize_constraint_store(Mks(mks.substitution, mks.counter, mks.diseq, cons(s, mks.symbols), mks.numbers, mks.absentee));
    }
}

function numbero(s) {
    return function(mks) {
        return normalize_constraint_store(Mks(mks.substitution, mks.counter, mks.diseq, mks.symbols, cons(s, mks.numbers), mks.absentee));
    }
}

function absento(s, f) {
    return function(mks) {
        return normalize_constraint_store(Mks(mks.substitution, mks.counter, mks.diseq, mks.symbols, mks.numbers, cons(cons(s,f), mks.absentee)));
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
        return (s !== false) && unify(u.cdr, v.cdr, s);
    } else {
        return (u == v) && s;
    }
}

function ext_s_check_prefix(x, v, s, cs) {
    if (occurs_check(x, v, s)) {
        return false;
    } else {
        return cons(s.set(x.c, v), cons(cons(x, v), cs));
    }
}

function unify_prefix(u, v, s, cs) {
    var u = walk(u, s);
    var v = walk(v, s);
    if (varp(u) && varp(v) && vareq(u, v)) { return cons(s, cs); }
    else if (varp(u)) { return ext_s_check_prefix(u, v, s, cs); }
    else if (varp(v)) { return ext_s_check_prefix(v, u ,s, cs); }
    else if (pairp(u) && pairp(v)) {
        var s_cs = unify_prefix(u.car, v.car, s, cs);
        return (s_cs !== false) && unify_prefix(u.cdr, v.cdr, s_cs.car, s_cs.cdr);
    } else {
        return (u == v) && cons(s, cs);
    }
}

function disequality(u, v, s) {
    var s_cs_hat = unify_prefix(u, v, s, null);
    if(s_cs_hat !== false) {
        var d = s_cs_hat.cdr;
        return (d == null) ? false : d;
    }
    else {
        return null;
    }
}

function normalize_constraint_store(mks) {
    var s = mks.substitution;
    var c = mks.counter;
    var d = mks.diseq;
    var dn = null;
    var sy = mks.symbols;
    var syn = null;
    var nm = mks.numbers;
    var nmn = null;
    var abs = mks.absentee;
    var absn = null;

    // Normalize the symbol set
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

    // Normalize the number set
    // ensure disjointness of symbols and numbers
    while(nm != null) {
        var i = walk(nm.car, s);
        nm = nm.cdr;
        
        if (varp(i)) {
            if(anyp(function(j){return vareq(j,i)}, syn)) {
                return mzero;
            }
            nmn = cons(i, nmn);
        }
        else if(numberp(i)) {
            continue;
        }
        else {
            return mzero;
        }
    }

    // normalize the disequality constraints
    while(d != null) {
        var es = d.car;

        if(es != null) {
            d_hat = disequality(map(car, es), map(cdr, es), s);
            
            if(d_hat === false) {
                return mzero;
            }

            dn = cons(d_hat, dn);
        }
        
        d = d.cdr;
    }

    // normalize the absento constraints
    while(abs != null) {
        var abs_s = walk(abs.car.car, s);
        var abs_f = walk(abs.car.cdr, s);
        
        if (varp(abs_s) && varp(abs_f)) {
            absn = cons(cons(abs_s, abs_f), absn);
        }
        else if (varp(abs_s) && symbolp(abs_f)) {
            // this could be changed into a =/= constraint
            absn = cons(cons(abs_s, abs_f), absn);
        }
        else if (symbolp(abs_s) && varp(abs_f)) {
            absn = cons(cons(abs_s, abs_f), absn);
        }
        else if (symbolp(abs_s) && symbolp(abs_f)) {
            if(abs_s == abs_f) {
                return mzero;
            }
            absn = cons(cons(abs_s, abs_f), absn);
        }
        else if (varp(abs_s) && pairp(abs_f)) {
            absn = cons(cons(abs_s, abs_f.car),
                        cons(cons(abs_s, abs_f.cdr), absn))
        }
        else {
            return mzero;
        }
        
        abs = abs.cdr;
    }

    return unit(Mks(s, c, dn, syn, nmn, absn));
}
 
function call_fresh(f) {
    return function(mks) {
        var c = mks.counter;
        return f(mkvar(c))(Mks(mks.substitution, (c + 1), mks.diseq, mks.symbols, mks.numbers, mks.absentee));
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
    return walk_star(v, reify_s(v, Immutable.Map()));
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
        return s.set(v1.c, reify_name(s.size));
    } else if (pairp(v1)) {
        return reify_s(v1.cdr, reify_s(v1.car, s));
    } else {
        return s;
    }
}

function reify_name(n) {
    return { toString: function() { return ["_", n].join("."); } };
}

function build_num(n) {
    if(n%2 == 1) {
        return cons(1, build_num(Math.floor((n-1)/2)));
    } else if ((!n == 0 ) && n%2 == 0) {
        return cons(0, build_num(Math.floor(n/2)));
    } else {
        return null;
    }
}
