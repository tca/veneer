var Immutable = require("./immutable.min.js");
var es = require('event-stream');
var vm = new VeneerVM();
/*
(define (appendo x y z)
 (conde
  ((== x '()) (== y z))
  ((fresh (head xtail ytail ztail)
    (== x `(,head . ,xtail))
    (== z `(,head . ,ztail))
    (appendo xtail y ztail)))))

*/

var myString = (function(){/*
(define (appendo x y z)
 (conde
  ((== x '()) (== y z))
  ((fresh (head xtail ytail ztail)
    (== x `(,head . ,xtail))
    (== z `(,head . ,ztail))
    (appendo xtail y ztail)))))




*/}).toString().slice(14,-3)

/*
(define (membero x l)
 (fresh (head tail)
  (== l `(,head . ,tail))
  (conde
   ((== x head))
   ((membero x tail)))))

(membero x '(1 2 3))

(define (appendo x y z)
 (conde
  ((== x '()) (== y z))
  ((fresh (head xtail ytail ztail)
    (== x `(,head . ,xtail))
    (== z `(,head . ,ztail))
    (appendo xtail y ztail)))))

(appendo left right '(1 2 3 4))
*/
console.log('myString', myString);
// var val = vm.read_eval("(== a 2)");
var sexpr = require('sexpression');
var exprs = require('s-expression');
try {
  console.log('s-expression', JSON.stringify(exprs(myString)));
  console.log('SEXPR', JSON.stringify(sexpr.parse(myString)));
  console.log('SEXPR re-stringified', sexpr.stringify(sexpr.parse(myString)));
  console.log('parsed 1', JSON.stringify(vm.parse_program(myString)));
  console.log('re-stringified', pretty_print(vm.parse_program(myString)));
  var val = vm.read_eval(myString);
  for (var x = 0 ; x < 5 ; x++) {
  var out = procedurep(val) ? val() : pretty_print(val);
    console.log(out);
  }
} catch (e) {
  console.error(e, val, myString);
}
