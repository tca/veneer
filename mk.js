function Var(c) { this.c = c; }
function mkvar(c) { return new Var(c); }
function varp(x) { return (x instanceof Var); }
function vareq(x1, x2) { return x1.c === x2.c; }

function MiniKanrenState(s, c, d, sy, nm, ab) {
    this.substitution = s;
    this.counter = c;
    this.diseq = d;
    this.symbols = sy;
    this.numbers = nm;
    this.absentee = ab;
}
function Mks(s, c, d, sy, nm, ab) { return new MiniKanrenState(s, c, d, sy, nm, ab); }

var not_found = [];
function walk(u, s) {
    var pr;
    while(varp(u)) {
        pr = s.get(u.c, not_found);
        if (pr === not_found) {
            return u;
        } else {
            u = pr;
        }
    } return u;
}

function occurs_check(x, v, s) {
    var v1 = walk(v, s);
    if(varp(v1)) {
        return vareq(v1, x);
    } else if (pairp(v1)) {
        return occurs_check(x, v1.car, s) || occurs_check(x, v1.cdr, s);
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
    };
}

function noteqeq(u, v) {
    return function(mks) {
        var d = disequality(u, v, mks.substitution);
        return d !== false ? unit(Mks(mks.substitution, mks.counter, cons(d, mks.diseq), mks.symbols, mks.numbers, mks.absentee)) : mzero;
    };
}

function symbolo(s) {
    return function(mks) {
        return normalize_constraint_store(Mks(mks.substitution, mks.counter, mks.diseq, cons(s, mks.symbols), mks.numbers, mks.absentee));
    };
}

function numbero(s) {
    return function(mks) {
        return normalize_constraint_store(Mks(mks.substitution, mks.counter, mks.diseq, mks.symbols, cons(s, mks.numbers), mks.absentee));
    };
}

function absento(s, f) {
    return function(mks) {
        return normalize_constraint_store(Mks(mks.substitution, mks.counter, mks.diseq, mks.symbols, mks.numbers, cons(cons(s, f), mks.absentee)));
    };
}

function unit(mks) { return cons(mks, mzero); }
var mzero = null;

function unify(u, v, s) {
    var u1 = walk(u, s);
    var v1 = walk(v, s);
    if (varp(u1) && varp(v1) && vareq(u1, v1)) { return s; }
    else if (varp(u1)) { return ext_s_check(u1, v1, s); }
    else if (varp(v1)) { return ext_s_check(v1, u1, s); }
    else if (pairp(u1) && pairp(v1)) {
        var s1 = unify(u1.car, v1.car, s);
        return (s1 !== false) && unify(u1.cdr, v1.cdr, s1);
    } else {
        return (u1 === v1) && s;
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
    var u1 = walk(u, s);
    var v1 = walk(v, s);
    if (varp(u1) && varp(v1) && vareq(u1, v1)) { return cons(s, cs); }
    else if (varp(u1)) { return ext_s_check_prefix(u1, v1, s, cs); }
    else if (varp(v1)) { return ext_s_check_prefix(v1, u1, s, cs); }
    else if (pairp(u1) && pairp(v1)) {
        var s_cs = unify_prefix(u1.car, v1.car, s, cs);
        return (s_cs !== false) && unify_prefix(u1.cdr, v1.cdr, s_cs.car, s_cs.cdr);
    } else {
        return (u1 === v1) && cons(s, cs);
    }
}

function disequality(u, v, s) {
    var s_cs_hat = unify_prefix(u, v, s, null);
    if(s_cs_hat !== false) {
        var d = s_cs_hat.cdr;
        return (d === null) ? false : d;
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
        var i1 = walk(nm.car, s);
        nm = nm.cdr;

        if (varp(i1)) {
            if(anyp(function(j) { return vareq(j, i1); }, syn)) {
                return mzero;
            }
            nmn = cons(i1, nmn);
        }
        else if(numberp(i1)) {
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
            var d_hat = disequality(map(car, es), map(cdr, es), s);

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
            if(abs_s === abs_f) {
                return mzero;
            }
            absn = cons(cons(abs_s, abs_f), absn);
        }
        else if (varp(abs_s) && pairp(abs_f)) {
            absn = cons(cons(abs_s, abs_f.car),
                        cons(cons(abs_s, abs_f.cdr), absn));
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
    };
}

function disj(g1, g2) {
    return function(mks) { return mplus(g1(mks), g2(mks)); };
}
function conj(g1, g2) {
    return function(mks) { return bind(g1(mks), g2); };
}
 
function mplus($1, $2) {
    if ($1 === null) {
        return $2;
    } else if (procedurep($1)) {
        return function() { return mplus($2, $1()); };
    } else {
        return cons($1.car, mplus($1.cdr, $2));
    }
}

function bind($, g) {
    if ($ === null) {
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
        var $1 = pull($);
        return ($1 === null) ? null : cons($1.car, take(n - 1, $1.cdr));
    }
}

function take_all($) {
    $ = pull($);
    return ($ === null) ? null : cons($.car, take_all($.cdr));
}

function reify(v, s) {
    var v1 = walk_star(v, s);
    return walk_star(v1, reify_s(v1, Immutable.Map()));
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


function intersperse_map(l, f, sep) {
    var m = [];
    while(l != null) {
        m = m.concat([f(l.car),(l.cdr == null) ? "" : sep]);
        l = l.cdr;
    }
    return m;
}

function query_map(qm, d, s) {
    var q = reify(cons(qm, d), s);
    var result = foldl(q.car, [], function(m, a_v) {
        return m.concat([a_v.car, ": ", pretty_print(a_v.cdr), "\n"]);
    });

    if(false) {
        return result;
    }
    else {
        var present = function(dd) {
            // dd is a disjunction of disequalities
            return pretty_print(cons(intern("or"),map(function(a){return list(intern("=/="),a.car,a.cdr)},dd)));
        };
        result = result.concat(["{"]);
        result = result.concat(intersperse_map(q.cdr, present, ","));
        result = result.concat(["}", "\n"]);
        return result;
    }
}

function build_num(n) {
    if((n % 2) === 1) {
        return cons(1, build_num(Math.floor((n - 1) / 2)));
    } else if (n !== 0 && (n % 2) === 0) {
        return cons(0, build_num(Math.floor(n / 2)));
    } else {
        return null;
    }
}
