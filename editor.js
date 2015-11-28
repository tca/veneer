function load_editor() {
    var veneer = new Veneer_v1();

    var vm = veneer.new_vm();

    var ed = veneer.new_editor(document.getElementById("container"), vm);
    var editor = ed.editor;
    var repl = ed.repl;
    var errors = ed.errors;
    var dump_button = ed.dump_button;

    var demo = false;
    var loaded_file = false;
    function setEditorValue(val) {
        demo = false;
        loaded_file = false;
        editor.setValue(val);
    }

    var demos = document.getElementsByClassName("demo");
    var demo_picker = document.getElementById("demo_picker");
    var file_values = new Array(demos.length);
    for(var i=0; i < demos.length; i++ ) {
        var selection = document.createElement("option");
        var name = demos[i].getElementsByClassName("title")[0].textContent;
        file_values[i] = demos[i].getElementsByClassName("content")[0].value;
        selection.value = i;
        selection.appendChild(document.createTextNode(name));
        demo_picker.appendChild(selection);
    }
    demo_picker.onchange = function() {
        load_demo(demo_picker.selectedIndex);
    };
    demo_picker.value = "0";
    setEditorValue(file_values[0]);
    demo = 0;

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

    document.getElementById("create_link").onclick = function() {
        var req = new XMLHttpRequest();
        var method = "POST";
        var url = "https://api.github.com/gists";

        var options = {
            "description": "veneer save",
            "public": true,
            "files": {
                "file": {
                    "content": editor.getValue()
                }
            }
        };

        req.open(method, url, true);
        req.onreadystatechange = function () {
            if (req.readyState !== XMLHttpRequest.DONE) {
                return;
            }
            alert(req.status);
            if (req.status === 201) {
                var response = JSON.parse(req.responseText);
                window.location.hash = response.id;
            }
        };
        req.send(JSON.stringify(options));
    };


    function confirm_overwrite(name) {
        return window.confirm("File exists: Are you sure you want to over-write  \"" + name + "\"");
    }
    function pick_filename() {
       return window.prompt("save file as:","default");
    }
    function confirm_save_progress() {
        return window.confirm("Save progress before switching?");
    }

    function load_demo(id) {
        var save_status = true;
        if (demo !== id) { save_status = save_current(true); }
        if(save_status) {
            var demo_val = file_values[id];
            setEditorValue(demo_val);
            demo = id;
        }
    }

    function load_file(name) {
        var save_status = true;
        if (loaded_file !== name) { save_status = save_current(true); }
        if(save_status) {
            var new_val = localStorage.getItem(name);
            setEditorValue(new_val);
            loaded_file = name;
        }
    }

    function save_current(for_change) {
        if (loaded_file !== false) {
            if(editor.getValue() !== localStorage.getItem(loaded_file)) {

                if(for_change === true && !confirm_save_progress()) {
                    return true;
                }

                loaded_file = confirm_overwrite(loaded_file) ? loaded_file : false;
            }
        } else if (demo !== false) {
            if (editor.getValue() !== file_values[demo]) {

                if(for_change === true && !confirm_save_progress()) {
                    return true;
                }

                loaded_file = window.prompt("save progress as: ", "default") || false;
            } else if (for_change === true) {
                return true;
            }
        }

        if(!loaded_file) { return false; }
        demo = false;

        if(files.indexOf(loaded_file) < 0) {
            files.push(loaded_file);

            var selection = document.createElement("option");
            selection.appendChild(document.createTextNode(loaded_file));
            ls_picker.appendChild(selection);
            ls_picker.value = loaded_file;
            localStorage.setItem('__index__', JSON.stringify(files));
        };
        localStorage.setItem(loaded_file, editor.getValue());
        return true;
    }

    function add_file() {
        if(save_current(true)) { setEditorValue(''); }
    }

    if(window.location.hash) {
        var req = new XMLHttpRequest();
        var method = "GET";
        var url = "https://api.github.com/gists/" + window.location.hash.substring(1);

        req.open(method, url, true);
        req.onreadystatechange = function () {
            if (req.readyState !== XMLHttpRequest.DONE) {
                return;
            }
            if (req.status === 200) {
                var response = JSON.parse(req.responseText);
                setEditorValue(response.files.file.content);
            }
        };
        req.send();
    }
}
