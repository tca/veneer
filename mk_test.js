
function fives(x) {
    return disj(eqeq(x, 5),
                function(a_c) {
                    return function() { return fives(x)(a_c); }
                });
}
function sixes(x) {
    return disj(eqeq(x, 6),
                function(a_c) {
                    return function() { return sixes(x)(a_c); }
                });
}


function node_log(x) { return console.log(require('util').inspect(x, true, 10)); }
var empty_state = cons(null, 0);
var test1 = call_fresh(function (q) { return eqeq(q, 5); })(empty_state);
node_log(test1.car);
node_log("-----");

var fv;
var sv;
var test2 = function(x) {
    fv = x;
    return fives(x);
};

var res = conj(call_fresh(test2), call_fresh(sixes))(empty_state);

node_log(assq(fv, take(5, res).car.car));

var x = ref(null);
var y = ref(null);
var foo = conj(call_fresh(function(z) { x.set(z); return eqeq(x.get(), y.get()) }),
               call_fresh(function(z) { y.set(z); return eqeq(y.get(), 1) }));

node_log(take(3, foo(empty_state)));

function appendo(l, s, out) {
    return disj(conj(eqeq(null, l), eqeq(s, out)),
               call_fresh(function(a) {
                   return call_fresh(function(d) {
                       return conj(eqeq(cons(a, d), l),
                                  call_fresh(function(res) {
                                      return conj(function(s_c) {
                                                      return function() {
                                                          return appendo(d,s,res)(s_c); };
                                                  }, eqeq(cons(a, res), out));
                                  })); 
                   });
               }));
}

var call_appendo =
    call_fresh(function(q) {
    return call_fresh(function(l) {
        return call_fresh(function(s) {
            return call_fresh(function(out) {
                return conj(appendo(l,s,out),
                            eqeq(list(l, s), q)); }); }); }); });

function pp(x) {
    if (pairp(x)) {
        return ["(", pp(x.car), ".", pp(x.cdr), ")"].join("");
    } else {
        return JSON.stringify(x);
    }
}

var test3 = call_fresh(function(a) { return appendo(list(1), a, list(1,2)); });
var test4 = call_fresh(function(q) { return call_fresh(function(b) { return call_fresh(function(a) { return conj(eqeq(list(a,b), q),
                                                                                                                 appendo(a, b, list(1,2,3))); }); }); });

console.log("--");
map(function(x) { return node_log(reify_first(x)); }, take(5, test4(empty_state)));
node_log(eqeq(1,1)(empty_state));
