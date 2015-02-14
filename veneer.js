function Veneer_v1() {
    this.new_editor = function(setup) {
        var options = { mode: "scheme",
                        matchBrackets: true,
                        autoCloseBrackets: true,
                        lineNumbers: true};
        return new CodeMirror(setup, options);
    };
 
    this.new_vm = function() { return new VeneerVM(); };
}
