
function extractVisibleText(t) {
    return t.split("/*****/\n")[0];
}

function updateEditorText(t, verifyIt) {
    ts = t.split("/*****/\n");
    if (ts.length > 1 && ts[1].length != 0) {   
        text = ts[1]
    } else {
        text = ts[0]
    }

    if (text.trim().startsWith("$")) {
        setText("")
        $.get(ts[1].trim().substring(1), function(data, status){
            setText(data)
            if (verifyIt) {
                verify()
            }    
        });        
    } else {
        setText(text);
        if (verifyIt) {
            verify()
        }    
}
}

function shouldVerify(t) {
    ts = t.split("/*****/\n");
    return ts.length > 2 && ts[2].startsWith("VERIFY");
}

function shouldBeBuggy(t) {
    ts = t.split("/*****/\n");
    return ts.length > 2 && ts[2].startsWith("VERIFY_BUG");
}


var highlight = ace.require("ace/ext/static_highlight")
var dom = ace.require("ace/lib/dom")

function htmlEntities(str) {
    return String(str).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');
}

$("pre.anchor").each(function (codeEl) {
    code = document.createElement('div');
    code.setAttribute("class", "col-11 my-2");
    outer = document.createElement('div');
    outer.setAttribute("class", "row p-0 m-0 bg-light border rounded")

    const text = this.innerText;
    const extracted = extractVisibleText(text);
    code.innerHTML = htmlEntities(extracted);

    buttonCol = document.createElement("div")
    buttonCol.setAttribute("class", "col-1 p-0 align-right")

    button = document.createElement("button")
    button.setAttribute("class", "btn btn-small btn-outline-dark p-0 px-1 pt-1  border-0")
    button.addEventListener("click", function() {
        this.blur();
        updateEditorText(text, false);
    });
    button.innerHTML = '<i class="far fa-copy"></i>'
    buttonCol.append(button)

    if (shouldVerify(text)) {
        button = document.createElement("button")
        button.setAttribute("class", "btn btn-small btn-outline-dark p-0 px-1 pt-1  border-0")
            button.addEventListener("click", function() {
            this.blur();
            updateEditorText(text, true);
        });
        if (shouldBeBuggy(text)) {
            button.innerHTML = '<i class="fas fa-bug"></i>'
        } else {
            button.innerHTML = '<i class="fas fa-anchor"></i>'
        }
        buttonCol.append(button)
    } 

    outer.append(buttonCol)

    // left = document.createElement("div")
    // left.setAttribute("class", "col-1 bg-light");

    outer.prepend(code);
    // outer.prepend(left);
    this.replaceWith(outer);

    highlight(code, {
        className: "lang-anchor",
        mode: "ace/mode/anchor",
        theme: "ace/theme/chrome",
        startLineNumber: 1,
        showGutter: false,
        trim: true,
        displayIndentGuides: false
    }, function (highlighted) {
    });
});

$("code.anchor").each(function (codeEl) {
    highlight(this, {
        className: "lang-anchor",
        mode: "ace/mode/anchor",
        theme: "ace/theme/chrome",
        startLineNumber: 1,
        showGutter: false,
        trim: true,
        displayIndentGuides: false
    }, function (highlighted) {
    });
});