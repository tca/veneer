function Veneer_v1() {
    this.new_editor = function(container, vm, seed) {
        var errors = document.createElement("div");
        errors.className += "errors";
        container.appendChild(errors);

        var options = { mode: "scheme",
                        matchBrackets: true,
                        autoCloseBrackets: true,
                        lineNumbers: true};
        var editor = new CodeMirror(function(ed) {
            container.appendChild(ed);
            return ed;
        }, options);
        
        var repl = document.createElement("div");
        repl.className += "repl";
        container.appendChild(repl);
        
        var dump_button = document.createElement("div");
        dump_button.className += "dump_button";
        dump_button.appendChild(document.createTextNode("run!"));
        container.appendChild(dump_button);

        var clear = document.createElement("hr");
        clear.className += "clear";
        container.appendChild(clear);
        
        var current_input = repl_getline(false);
        function display_error(e) {
            var error = document.createElement("div");
            var error_txt = document.createTextNode(e);
            error.className += "error";
            error.appendChild(error_txt);
            errors.appendChild(error);
            setTimeout(function() { errors.removeChild(error); }, 3000);
        }

        function load_input(inputbox) {
            inputbox = current_input;
            /* var textcontent = inputbox.innerHTML.replace(/<br(\s*)\/*>/ig, '\n') 
               .replace(/<[p|div]\s/ig, '\n$0') 
               .replace(/(<([^>]+)>)/ig, ""); */
            var textcontent = inputbox.textContent;
            try {
                var generator = vm.read_eval(textcontent);
                var result_elt = document.createElement("div");
                result_elt.className += "result";
                var answer_text = document.createElement("div");
                var button = document.createElement("button");
                var append_answer = function(focus) { 
                    var time_before = window.performance.now();
                    var result_val = generator();
                    var run_time = (window.performance.now() - time_before).toFixed(2);
                    if (result_val==null) { result_elt.removeChild(button); result_val = "No."; }
                    var result_val_pp = "Yes. (" + run_time + "ms) \n" + result_val;
                    var result = document.createTextNode("=> " + result_val_pp + "\n");
                    
                    answer_text.appendChild(result);
                    if(focus) {
                        button.focus();
                        current_input.scrollIntoView(false);
                    }

                    return false;
                }
                button.onclick = function() { return append_answer(true); };
                button.appendChild(document.createTextNode("More answers!"));

                result_elt.appendChild(answer_text);
                result_elt.appendChild(button);
                append_answer(false);
                repl.appendChild(result_elt);

                inputbox.contentEditable = false;
                repl_getline(true);
                return false;
            } catch (e) {
                if(e instanceof ReaderError) {
                    inputbox.appendChild(document.createTextNode("\n"));
                    display_error(e.msg);
                    return true;
                } else {
                    display_error(e);
                    throw e;
                }
            }
        }

       
        function repl_getline(focus) {
            var inputbox = document.createElement("pre");
            inputbox.className += "inputbox";
            inputbox.contentEditable = true;
            inputbox.onkeypress = function(e) {
                if (e.keyCode == 13) {
                    return load_input(inputbox);
                }
            };

            repl.appendChild(inputbox);
            if (focus) { inputbox.focus(); }
            current_input = inputbox;
            return inputbox;
        }
        

        var dump_editor = function() {
            vm.reset();
            if (!(typeof seed === 'undefined')) { vm.read_eval(seed); }
            current_input.textContent = editor.getValue();
            load_input(current_input);
            return false;
        }
        dump_button.onclick = dump_editor;

        var shift = false;

        editor.setOption("extraKeys", {
            "Shift-Enter": function(cm) { dump_editor();}
        });

        return { editor: editor, repl: repl, errors: errors, dump_button: dump_button };
    };

 
    this.new_vm = function() { return new VeneerVM(); };
}
