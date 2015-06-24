
var Immutable = require("./immutable.min.js");
var es = require('event-stream');
var VeneerVM = require('./eval');
var read_program = require('./reader');
var fs = require('fs');
var runtime = require('./base');
// var VeneerVM = require('./veneer');
console.log('loading');

function inputs (input) {
  var L = [ ];
  console.log('inputs to inputs', arguments);
  var out = es.through(function (d) { this.queue(d); });
  if (!input) {
    L.push(process.stdin);
  } else {
    var args = [].slice.apply([], arguments);
    if (args && args.length > 0) {
      L = L.concat(args);
    }
  }

  function iter (elem, next) {
    var from = elem;
    if (!from.pipe) {
      from = fs.createReadStream(elem)
        .on('end', function (ev) {return next( );})
        ;
    }
    from.pipe(out, {end: false });
  }

  function ender (err, remainder) {
    console.log('finished everything', err, remainder);
    out.end( );
  }

  es.pipeline(
    es.readArray(L)
  , es.map(iter)
  , es.writeArray(ender)
  );
  return out;
}

function lines ( ) {
  return es.split( );
}

function get_ast (vm) {
  var line = [ ];
  function iter (data) {
    try {
      this.queue(vm.parse_program(data));
    } catch (e) {
      console.error(e);
    }
  }
  return es.through(iter);
}

function tap (prefix) {
  function iter (data, next) {
    console.log(prefix, data);
    return next(null, data);
  }
  return es.map(iter);
}

if (!module.parent) {
  console.log('hello world');
  var vm = new VeneerVM(read_program, runtime);
  console.log(vm);
  es.pipeline(
    inputs.apply(this, process.argv.slice(3))
  , lines( )
  , get_ast(vm)
  , tap('xxx?')
  );
}
