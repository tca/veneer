function Var(c) { this.c = c; }
function mkvar(c) { return new Var(c); }
function varp(x) { return (x instanceof Var); }
function vareq(x1, x2) { return x1.c === x2.c; }

function MiniKanrenState(s, c, d, ty, ab, w) {
    this.substitution = s;
    this.counter = c;
    this.diseq = d;
    this.types = ty;
    this.absentee = ab;
    this.watch = w;
}
function Mks(s, c, d, ty, ab, w) { return new MiniKanrenState(s, c, d, ty, ab, w); }

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
        return s !== false ? normalize_constraint_store(Mks(s, mks.counter, mks.diseq, mks.types, mks.absentee, mks.watch)) : mzero;
    };
}

function noteqeq(u, v) {
    return function(mks) {
        var d = disequality(u, v, mks.substitution);
        return d !== false ? unit(Mks(mks.substitution, mks.counter, cons(d, mks.diseq), mks.types, mks.absentee, mks.watch)) : mzero;
    };
}

function type_check(v, p, s, ty) {
    var v1 = walk(v, s);
    if (varp(v1)) {
        var existing_type = ty.get(v1, false);
        if(existing_type && existing_type !== p) {
            return false;
        } else { // add constraint
            return ty.set(v1, p);
        }
    } else { // ground; run test
        return p(v1) ? ty : false;
    }
}

function symbolo(s) { return typeo(s, symbolp); }
function numbero(n) { return typeo(n, numberp); }

function typeo(v, p) {
    return function(mks) {
        var s = mks.substitution;
        var ty = mks.types;
        var ty1 = type_check(v, p, s, ty);
        if (!ty1) {
            return mzero;
        } else if (ty1 === ty) {
            return unit(mks);
        } else {
            var mks1 = Mks(mks.substitution, mks.counter, mks.diseq, ty1, mks.absentee, mks.watch);
            return normalize_constraint_store(mks1);
        }
    };
}

function absento(s, f) {
    return function(mks) {
        return normalize_constraint_store(Mks(mks.substitution, mks.counter, mks.diseq, mks.types, cons(cons(s, f), mks.absentee, mks.watch)));
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

function watch_collect(xs, k) {
    return function(s) {
        var xs1 = walk(xs, s);
        if(varp(xs1)) { return watch_collect(xs1, k); }
        else if(pairp(xs)) {
            var k1 = function(x, s) {
                var k2 = function(y, s) { return k(cons(x,y), s); };
                return watch_collect(cdr(xs), k2)(s);
            };
            return watch_collect(car(xs), k1)(s);
        }
        else { return k(xs, s); }
    };
}

function watch(x, g) {
   return function(mks) {
       var g1 = function(val) { return function(mks) { return g[0]([val], g[1])(mks); }; };
       var k = function(val,s) { return [g1(val)]; };
       var watches = cons(watch_collect(x, k), mks.watch);
       var mks1 = Mks(mks.substitution, mks.counter, mks.diseq, mks.types, mks.absentee, watches);
       return normalize_surveilence(mks1);
   }
}

function normalize_surveilence(mks) {
    var ws = mks.watch;
    var wn = null;
    var done = null;

    // for each watched var:
    // 1. if stream is empty, execute constraint
    // 2. else re-queue watch at this position
    while (ws !== null && ws !== undefined) {
        // pick out a watch
        var w = car(ws)(mks.substitution);
        if(procedurep(w)) { // requeue and break
            wn = cons(w, wn);
        } else { // done
            done = cons(w[0], done);
        }
        ws = cdr(ws);
    }

    // run all todo
    function execute_goals(gs) {
        return function(mks) {
            if (gs === null) {
                return unit(mks);
            } else {
                return bind(car(gs)(mks), execute_goals(cdr(gs)));
            }
        }
    };

    var mks1 = Mks(mks.substitution, mks.counter,mks.diseq, mks.types, mks.absentee, wn);
    return execute_goals(done)(mks1);
}

function normalize_constraint_store(mks) {
    return bind(normalize_surveilence(mks), normalize_constraint_store1);
}


function normalize_constraint_store1(mks) {
    var s = mks.substitution;
    var c = mks.counter;
    var d = mks.diseq;
    var dn = null;
    var ty = mks.types;
    var tyn = Immutable.Map();
    var abs = mks.absentee;
    var absn = null;
    var ws = mks.watch;

    // Normalize the type constraints
    ty.forEach(function(p, v) {
        tyn = type_check(v, p, s, tyn);
        return tyn;
    });
    if (!tyn) { return mzero; }

    // normalize the disequality constraints
    while(d !== null) {
        var es = d.car;

        if(es !== null) {
            var d_hat = disequality(map(car, es), map(cdr, es), s);

            if(d_hat === false) {
                return mzero;
            }

            dn = cons(d_hat, dn);
        }

        d = d.cdr;
    }

    // normalize the absento constraints
    while(abs !== null) {
        var abs_cur = abs.car;
        abs = abs.cdr;

        var abs_s = walk(abs_cur.car, s);
        var abs_f = walk(abs_cur.cdr, s);

        // defer until both terms are ground
        if (varp(abs_f) || varp(abs_s)) {
            absn = cons(cons(abs_s, abs_f), absn);
        }
        // split and requeue
        else if (pairp(abs_f)) {
            abs = cons(cons(abs_s, abs_f.car),
                       cons(cons(abs_s, abs_f.cdr), abs ));
        }
        // both are ground and atomic; check for eqv?
        else if (abs_s === abs_f) {
            return mzero;
        }
        // forget constraint, it can never fail
    }

    return unit(Mks(s, c, dn, tyn, absn, ws));
}

function call_fresh(f) {
    return function(mks) {
        var c = mks.counter;
        return f(mkvar(c))(Mks(mks.substitution, (c + 1), mks.diseq, mks.types, mks.absentee, mks.watch));
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


function disj_dfs(g1, g2) {
    return function(mks) { return mplus_dfs(g1(mks), g2(mks)); };
}

function conj_dfs(g1, g2) {
    return function(mks) { return bind_dfs(g1(mks), g2); };
}

function mplus_dfs($1, $2) {
    if ($1 === null) {
        return $2;
    } else if (procedurep($1)) {
        return function() { return mplus_dfs($1(), $2); };
    } else {
        return cons($1.car, mplus_dfs($1.cdr, $2));
    }
}

function bind_dfs($, g) {
    if ($ === null) {
        return mzero;
    } else if (procedurep($)) {
        return function() { return bind_dfs($(), g); };
    } else {
        return mplus_dfs(g($.car), bind_dfs($.cdr, g));
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

function pred_to_tag(p) {
    return assq(p, list(cons(symbolp, intern("sym")),
                        cons(numberp, intern("num")))).cdr;
}

function query_map(qm, mks) {
    var s = mks.substitution;
    var d = mks.diseq;
    var t = mks.types;
    // convert the type store to alist
    var t1 = t.reduce(function(m, v, k) { return cons(cons(k, v), m); }, null);

    var sq1 = walk_star(qm, s);
    var dq1 = walk_star(d, s);
    var tq1 = walk_star(t1, s);
    var q = walk_star(list(sq1, dq1, tq1), reify_s(list(sq1, dq1, tq1), Immutable.Map()));

    return print_constraints(q.car, q.cdr.car, q.cdr.cdr.car, s);
}

function print_constraints(sq, dq, tq, s) {
    var subs = foldl(sq, [], function(m, a_v) {
        return m.concat([a_v.car, ": ", pretty_print(a_v.cdr), "\n"]);
    });

    var present_d = function(dd) {
        // dd is a disjunction of disequalities
        var diseqs = map(function(a){ return list(intern("=/="), a.car, a.cdr); }, dd);
        if (length(diseqs) > 1) {
            return pretty_print(cons(intern("or"), diseqs));
        } else if (diseqs !== null) {
            return pretty_print(diseqs.car);
        } else {
            return null;
        }
    };
    var present_t = function(tt) {
        return pretty_print(list(pred_to_tag(tt.cdr), tt.car));
    }
    return (dq !== null || tq !== null) ?
        (subs
         .concat(["{"])
         .concat(intersperse_map(dq, present_d, ", "))
         .concat([", "])
         .concat(intersperse_map(tq, present_t, ", "))
         .concat(["}\n"]).join("")) :
        subs.join("");
}

function intersperse_map(l, f, sep) {
    var m = [];
    var r;
    while(l !== null) {
        r = f(l.car);
        m = r === null ? m : m.concat([r, (l.cdr === null ? "" : sep)]);
        l = l.cdr;
    }
    return m;
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
