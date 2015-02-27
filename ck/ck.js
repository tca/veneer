function Var(c) { this.c = c; }
function mkvar(c) { return new Var(c); }
function varp(x) { return (x instanceof Var); }
function vareq(x1, x2) { return x1.c === x2.c; }

function MiniKanrenState(s, c, p, cs) {
    this.substitution = s;
    this.counter = c;
    this.prefix = p;
    this.constraint_store = cs;
}
function Mks(s, c, p, cs) { return new MiniKanrenState(s, c, p, cs); }

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

function unify(u, v, mks) {
    var s = mks.substitution;
    var p = mks.prefix;
    var u1 = walk(u, s);
    var v1 = walk(v, s);
    if (varp(u1) && varp(v1) && vareq(u1, v1)) { return mks; }
    else if (varp(u1)) { return ext_s_check_prefix(u1, v1, mks); }
    else if (varp(v1)) { return ext_s_check_prefix(v1, u1, mks); }
    else if (pairp(u1) && pairp(v1)) {
        var mks1 = unify(u1.car, v1.car, mks);
        return (mks1 !== false) && unify(u1.cdr, v1.cdr, mks1);
    } else {
        return (u1 === v1) && mks;
    }
}

function eqeq(u, v) {
    return function(mks) {
        var mks1 = unify(u, v, mks);
        return mks1 === false ? mzero : run_constraints(mks1);
    };
}

var empty_set = Immutable.Set();
function ext_disequality(u, v, mks) {
    var cs = mks.constraint_store;
    return Mks(mks.substitution, mks.counter, mks.prefix,
               cs.updateIn([u.c, 1], empty_set, function(ds) { return ds.add(v); }));
}
function rem_disequality(u, v, mks) {
    var ds1 = mks.constraint_store.getIn([u.c, 1], false);
    if (ds1) {
        return Mks(mks.substitution, mks.counter, mks.prefix, mks.constraint_store.setIn([u.c, 1],  ds1.delete(v)));
    } else {
        return mks;
    }
}

// need to do more for =/= between vars?
function disunify(u, v, mks) {
    var s = mks.substitution;
    var p = mks.prefix;
    var u1 = walk(u, s);
    var v1 = walk(v, s);
    if (varp(u1) && varp(v1) && vareq(u1, v1)) { return false; }
    else if (varp(u1)) { return ext_disequality(u1, v1, mks); }
    else if (varp(v1)) { return ext_disequality(v1, u1, mks); }
    else if (pairp(u1) && pairp(v1)) {
        var mks1 = disunify(u1.car, v1.car, mks);
        return (mks1 !== false) && disunify(u1.cdr, v1.cdr, mks1);
    } else {
       if (u1 !== v1) {
           if (varp(u)) {
               return rem_disequality(u, v1, mks);
           } else { return mks; }
       } else {
           return false;
       }
    }
}

function disequality(u, vs, mks) {
    var mks1 = mks;
    vs.forEach(function(v) {
        mks1 = disunify(u, v, mks);
        return mks1;
    });
    return mks1;
}

function noteqeq(u, v) {
    return function(mks) {
        var mks1 = disunify(u, v, mks);
        return mks1 !== false ? unit(mks1) : mzero;
    };
}

var empty_map = Immutable.Map();
function type_check(v, p, mks) {
    var s = mks.substitution;
    var cs = mks.constraint_store;
    var v1 = walk(v, s);
    if (varp(v1)) {
        var cs_entry = cs.get(v1.c, false);
        var existing_type = cs_entry !== false && cs_entry.get(0, false);
        if (existing_type && existing_type !== p) {
            if(existing_type === p) {
                // types match, dont add extra constraint
                return mks;
            } else {
                // type mismatch; fail
                return false;
            }
        } else {
            // add constraint
            cs_entry = cs_entry || empty_map;
            var cs1 = cs.set(v1.c, cs_entry.set(0, p));
            return Mks(s, mks.counter, mks.prefix, cs1);
        }
    } else {
        // ground; run test
        if (p(v1)) {
            var cs1 = cs;
            if (varp(v)) {
                // remove constraint from store; it cannot be violated
                var cs_entry = cs.get(v.c, false);
                cs1 = cs_entry ? cs.set(v.c, cs_entry.delete(0)) : cs;
            }
            return Mks(s, mks.counter, mks.prefix, cs1);
        } else {
            return false;
        }
    }
}

function typeo(v, p) {
    return function(mks) {
        var mks1 = type_check(v, p, mks);
        return mks1 === false ? mzero : unit(mks1);
    };
}

function symbolo(s) { return typeo(s, symbolp); }
function numbero(n) { return typeo(n, numberp); }

function absent_check(u, v, mks) {
    var s = mks.substitution;

    var abs_f = walk(u, s);
    var abs_s = walk(v, s);

    // defer until both terms are ground
    if (varp(abs_f) || varp(abs_s)) {
        var cs2 = mks.constraint_store.updateIn([abs_f.c, 2], function(_) { return abs_s; });
        return vareq(abs_s, abs_f) ? false : Mks(s, mks.counter, mks.prefix, cs2);
    }
    // split and requeue
    else if (pairp(abs_f)) {
        var mks1 = Mks(s, mks.counter, mks.prefix, mks.constraint_store.deleteIn([abs_f.c, 2]));
        var mks2 = absent_check(abs_f.car, abs_s, mks1);
        return mks2 !== false && absent_check(abs_f.car, abs_s, mks2);
    }
    // both are ground and atomic; check for eqv?
    else if (abs_s === abs_f) {
        return false;
    } else {
        // forget constraint, it can never fail
        return Mks(s, mks.counter, mks.prefix, mks.constraint_store.deleteIn([abs_f, 2]));
    }
}

function absento(s, f) {
    return function(mks) {
        var mks1 = absent_check(f, s, mks);
        return mks1 !== false ? unit(mks1) : mzero;
    };
}

function unit(mks) { return cons(mks, mzero); }
var mzero = null;

function ext_s_check_prefix(x, v, mks) {
    var s = mks.substitution;
    var p = mks.prefix;
    if (occurs_check(x, v, s)) {
        return false;
    } else {
        return Mks(s.set(x.c, v), mks.counter, cons(cons(x, v), p), mks.constraint_store);
    }
}

var ctable = [type_check, disequality, absent_check];

function run_constraints(mks) {
    var cs = mks.constraint_store;
    if (cs.isEmpty()) { return unit(mks); }

    var s = mks.substitution;
    var c = mks.counter;
    var p = mks.prefix;
    var mks1 = Mks(s, c, null, cs);
   
    // TODO: add loop to run changes added by constraints ?
    var relevant_cs;
    while(p !== null) {
        relevant_cs = cs.get(p.car.car.c, false);
        if (relevant_cs) {
            relevant_cs.forEach(function(ct, cv) {
                mks1 = ctable[cv](p.car.car, ct, mks1);
                return mks1;
            });
            if(!mks1) { return mzero; }
        }
        p = p.cdr;
    }
    return unit(mks1);
}

function call_fresh(f) {
    return function(mks) {
        var c = mks.counter;
        return f(mkvar(c))(Mks(mks.substitution, (c + 1), mks.prefix, mks.constraint_store));
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

function pred_to_tag(p) {
    return assq(p, list(cons(symbolp, intern("sym")),
                        cons(numberp, intern("num")))).cdr;
}

function query_map(qm, mks) {
    var s = mks.substitution;
    
    var q = reify(qm, s);

    var m =  print_constraints(q, s);
    
    return m;
}

function print_constraints(sq, s) {
    var subs = foldl(sq, [], function(m, a_v) {
        return m.concat([a_v.car, ": ", pretty_print(a_v.cdr), "\n"]);
    });

    return subs.join("");
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
