function load_editor() {
    var veneer = new Veneer_v1();

    var vm = veneer.new_vm();

    var ed = veneer.new_editor(document.getElementById("container"), vm);
    var editor = ed.editor;
    var repl = ed.repl;
    var errors = ed.errors;
    var dump_button = ed.dump_button;

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
