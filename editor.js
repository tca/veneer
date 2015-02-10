function load_editor() {
    var errors = document.getElementById("errors");
    function display_error(e) {
        var error = document.createElement("div");
        var error_txt = document.createTextNode(e);
        error.className += "error";
        error.appendChild(error_txt);
        errors.appendChild(error);
        setTimeout(function() { errors.removeChild(error); }, 3000);
    }

    var options = { mode: "scheme",
                    matchBrackets: true,
                    autoCloseBrackets: true,
                    lineNumbers: true};
    var editor = false;
    var load_editor = function(ed) {
        document.body.insertBefore(ed, document.getElementById("repl"));
        return ed;
    };
    editor = new CodeMirror(load_editor, options);
    //editor.setSize("90%", "50%");
    var repl = document.getElementById("repl");
    var current_input =  repl_getline();;
    
    function load_input(inputbox) {
        /* var textcontent = inputbox.innerHTML.replace(/<br(\s*)\/*>/ig, '\n') 
           .replace(/<[p|div]\s/ig, '\n$0') 
           .replace(/(<([^>]+)>)/ig, ""); */
        var textcontent = inputbox.textContent;
        try {
            var generator = run_program(read_program(textcontent));
            var result_elt = document.createElement("pre");
            result_elt.className += "result";
            var answer_text = document.createElement("pre");
            var button = document.createElement("button");
            var append_answer = function() { 
                var result_val = generator();
                if (result_val==null) { result_elt.removeChild(button); result_val = "No."; }
                var result_val_pp = "Yes.\n" + result_val;
                var result = document.createTextNode("=> " + result_val_pp + "\n");
                
                answer_text.appendChild(result);
                button.focus();
                button.scrollIntoView();
                return false;
            }
            button.onclick = append_answer;
            button.appendChild(document.createTextNode("More answers!"));

            result_elt.appendChild(answer_text);
            result_elt.appendChild(button);
            append_answer();
            repl.appendChild(result_elt);

            inputbox.contentEditable = false;
            repl_getline();
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

    function repl_getline() {
        var inputbox = document.createElement("pre");
        inputbox.className += "inputbox";
        inputbox.contentEditable = true;
        inputbox.onkeypress = function(e) {
            if (e.keyCode == 13) {
                return load_input(inputbox);
            }
        };
        repl.appendChild(inputbox);
        inputbox.focus();
        inputbox.scrollIntoView();
        current_input = inputbox;
        return inputbox;
    }
    
    var dump_button = document.getElementById("dump_button");

    var load_editor = function() {
        var editor_value = editor.getValue();
        toplevel = new Object(null);
        current_input.textContent = editor_value;
        load_input(current_input);
        return false;
    }
    dump_button.onclick = load_editor;

    var loaded_file = false;
    function setEditorValue(val) {
        loaded_file = false;
        editor.setValue(val);
    }

    var demos = document.getElementsByClassName("demo");
    var demo_picker = document.getElementById("demo_picker");
    var file_values = new Array(demos.length);
    for(var i=0; i < demos.length; i++ ) {
        var selection = document.createElement("option");
        var name = demos[i].getElementsByClassName("title")[0].textContent;
        file_values[i] =  demos[i].getElementsByClassName("content")[0].value;
        selection.value = i;
        selection.appendChild(document.createTextNode(name));
        demo_picker.appendChild(selection);
    }
    demo_picker.onchange = function() { setEditorValue(file_values[demo_picker.selectedIndex]); };
    demo_picker.value = "0";
    setEditorValue(file_values[0]);

    var ls_picker = document.getElementById("localstorage_picker");
    var files = JSON.parse(localStorage.getItem('__index__') || "[]");
    for(var i=0; i < files.length; i++ ) {
        var selection = document.createElement("option");
        var name = files[i];
        selection.value = name;
        selection.appendChild(document.createTextNode(name));
        ls_picker.appendChild(selection);
    }
    ls_picker.onchange = function() {
        load_file(ls_picker[ls_picker.selectedIndex].value);
    };
    document.getElementById("save_file").onclick = save_current;
    document.getElementById("new_file").onclick = add_file;
    
    function load_file(name) {
        var new_val = localStorage.getItem(name);
        setEditorValue(new_val);
        loaded_file = name;
    }

    function confirm_overwrite(name) {
        return window.confirm("File exists: Are you sure you want to over-write  \"" + name + "\"");
    }
    function save_current() {
        if(loaded_file) {
            var overwrite = confirm_overwrite(loaded_file);
            if(!overwrite) { return false; }
        } else {
            loaded_file = window.prompt("save file as:","default");
            if(localStorage.getItem(loaded_file) && !confirm_overwrite(loaded_file)) {
                return false;
            }
        }
        if(files.indexOf(loaded_file) < 0) {
            files.push(loaded_file);

            var selection = document.createElement("option");
            selection.appendChild(document.createTextNode(loaded_file));
            ls_picker.appendChild(selection);
            ls_picker.value = loaded_file;
            localStorage.setItem('__index__', JSON.stringify(files));
        };
        localStorage.setItem(loaded_file, editor.getValue());
    } 

    function add_file() {
        save_current();
        setEditorValue('');
        save_current();
    }
}
