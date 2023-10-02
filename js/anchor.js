function query(url, data, success) {
    $.post(url, data).done(function(json) {
        endVerify()
        success(json)
    }).fail(function(hr, textStatus, error) {
        endVerify()
        var err = "Error " + hr.status + ": " + textStatus + ", " + error
        console.log(err)
     //   document.getElementById("status").innerHTML = 'Bad Response: ' + textStatus
        // document.getElementById("status").innerHTML = 'Server Timeout or Failure'
        success(JSON.parse(`
        { 
            "Status" : "Timed Out or Network Failure",
            "Errors" : [
               {
                "line" : 1,
                "column" : 1,
                "message" : "The Anchor Verifier web service limits the compute time per query.  Install Anchor locally if timeouts persist for your programs.  See <a target=\\"_blank\\" href=\\"https://doi.org/10.5281/zenodo.4032624\\">here</a> for details."
               }
            ]
        }
        `))
    })
}

function changeHeap(heap) {
    console.log(heap)
    document.getElementById("heap").src = heap
}

var counter = 0;

function uniqueId() {
    counter++;
    return `id${counter}`
}

function rescaleImage(id) {
    document.getElementById(id).style.width = '200%';
}

function genHeapButton(heap) {
    id = uniqueId()
    if (heap) {
        heapButton = `
          <button class="btn btn-warning btn-small btn-heap" type="button" data-toggle="collapse" data-target="#${id}" aria-expanded="false" aria-controls="${id}">
            <i class="fas fa-sitemap"></i>
          </button>
        `
            // 
        heapRow = `
          <div class="row collapse overflow-auto border mx-3 mt-1" id="${id}"  onclick="$('#${id}').collapse('toggle')">
            <div class="overflow-auto col-12"  style="max-height: 500px;">
              <img class="heap-image" src='${heap}' id="${id}-img">
            </div>
          </div>
        `
    } else {
        heapButton = `
          <button type="button" class="btn btn-warning btn-small btn-heap invisible">
            <i class="fas fa-sitemap"></i>
          </button>
        `
        heapRow = `
        `
    }
    return [heapButton, heapRow];
}

function genMoverButton(mover, justification, color = "success") {
    m = mover
    switch (mover) {
        case "B":
            m = `<i class="fas fa-arrows-alt-h"></i>`
            m = "B"
            break;
        case "L":
            m = `<i class="fa fa-arrow-left"></i>`
            m = "L"
            break;
        case "R":
            m = `<i class="fa fa-arrow-right"></i>`
            m = "R"
            break;
        case "N":
            m = `N`
            break;
        case "E":
            m = `<i class="fa fa-times"></i>`
            m = "E"
            break;
        case "=":
            m = "Y"
            break;
        default:
            m = mover
    }
    if (mover && justification.preds) {
        justificationText = justification.preds ? justification.preds.join("<br>") : ""
        moverButton = `
          <a tabindex="0" role="button" class="btn btn-${color} btn-small btn-mover rounded-circle ${mover ? "" : "invisible"}" 
                  data-toggle="popover" data-placement="left" data-html="true"  data-trigger="focus"
                  data-title="${justification.access}"
                  data-content="${justificationText}">
            ${m}
          </a>
          `
    } else if (mover && mover == "=") {
        moverButton = `
          <a tabindex="0" role="button" class="btn btn-primary btn-small btn-mover ${mover == "" ? "invisible" : "disabled"}">
            ${mover == "" ? "x" : m}
          </a>
          `
    } else {
        moverButton = `
          <a tabindex="0" role="button" class="btn btn-success btn-small btn-mover rounded-circle ${(!mover || mover == "") ? "invisible" : "disabled"}">
            ${(!mover || mover == "") ? "x" : m}
          </a> 
          `
    }
    return moverButton
}

function genError(x) {
    if (x.trace) {
        body = genTraceError(x)
    } else {
        body = ""
    }

    id = uniqueId()
    return `<li class="h4 text-wrap"> 
  <a onclick="gotoLine(${x.line})">${x.line}</a> : <a onclick="$('#${id}').collapse('toggle')">${x.message}</a>
    <div class="collapse show" id="${id}">
      <div class="mt-2 mb-3">
        ${body}
      </div>
    </div>
  </li>  
  `
}

function gotoLine(line) {
    if (line != "t:" && line != "u:") {
        editor.gotoLine(line);
    }
}


function genTraceError(x) {
    return x.trace.map(function(x) {
        if (x.text) {
            return `
          <div class="row mb-2">
            <div class="col-1"> 
            </div> 
            <div class="col p-0 pr-3"> 
              ${x.text}
            </div>
          </div>
          `
        } else {
            moverButton = genMoverButton(x.mover, x.justification, x.color)
            const [heapButton, heapRow] = genHeapButton(x.heap);
            const cls = x.line == "t:" ? "t-step" : x.line == "u:" ? "u-step" : ""
            const scr = x.line == "t:" ? "" : x.line == "u:" ? "" : `onclick="gotoLine(${x.line})"`

            toggleButton = ""

            switch (x.extra) {
                case "POP":
                    stmt = x.stmt;
                    inlinedRow = "</div>";
                    break;
                case "PUSH":
                    id = uniqueId();
                    stmt = `<a onclick="$('#${id}').collapse('toggle')">${x.stmt}</a>`;

                    moverButton = `
          <button class="btn btn-small btn-fold btn-light" type="button" data-toggle="collapse" data-target="#${id}" aria-expanded="false" aria-controls="${id}">
            <i class="fas fa-ellipsis-h"></i>
          </button>
          `
                    inlinedRow = `<div class="collapse hide" id="${id}">`;
                    break;
                default:
                    stmt = x.stmt
                    inlinedRow = ""
            }

            return `
          ${heapRow}
          <div class="row flex-nowrap">
            <div class="col-2 text-truncate"> 
              <div class="text-right"> 
                <code class="${cls}" ${scr}> 
                 ${x.line} 
                </code> 
              </div> 
            </div>
            <div class="col-auto p-0"> 
              ${moverButton}
              ${heapButton}
              ${toggleButton}
              </div>
            <div class="col-auto"> <code class="${cls}" ${scr}> ${stmt} </code> </div>
          </div>
          ${inlinedRow}
          `
        }
    }).join("")
}

function update(json) {
    document.getElementById("status").innerHTML = json.Status + (json.Time !== undefined ? "   (" + json.Time + ")" : "")
    errors = json.Errors.map(genError).join("")
    document.getElementById("errors").innerHTML = errors
    $(document).ready(reset);
    editor.resize()
}

function reset() {
    $('[data-toggle="tooltip"]').tooltip();
    $('[data-toggle="popover"]').popover();
}

function verify() {
    const url = 'http://bestwebever.me:8080/verify'
    const text = editor.getValue();
    $('.popover').popover('hide');
    startVerify()
    query(url, text, update)
}

function startVerify() {
    document.getElementById("verify-button").innerHTML = `<div class="spinner-border text-primary spinner-border mt-3 mb-3"></div>`
}

function endVerify() {
    document.getElementById("verify-button").innerHTML =
        `<button type="button" class="btn btn-primary" id="Verify" onclick="verify()">Verify</button>`
}

endVerify()
var editor = ace.edit("editor");
editor.setTheme("ace/theme/chrome");
editor.session.setMode("ace/mode/anchor");
editor.renderer.setOption("showFoldWidgets", false);
editor.renderer.setOption("minLines", 10);
editor.session.setTabSize(2);
editor.renderer.setOption("fontSize", "16px");
editor.renderer.setOption("printMargin", false);
editor.renderer.setOption("displayIndentGuides", false);
editor.setOptions({
    enableBasicAutocompletion: true,
    enableSnippets: true,
})

$(document).ready(reset());
$(document).ready(editor.resize());

function loadFile(x) {
    $.get(x).done(data => {
        editor.session.setValue(data);
        reset();
    });
}

function setText(x) {
    editor.session.setValue(x);
}

$(document).ready(function() {
    $.get('./examples/').done(data => {
        document.getElementById("examples").innerHTML =
            data.map(function(x) {
                file = `./examples/${x}`
                scr = `loadFile("${file}")`;
                return `<a class="dropdown-item" href="#" onclick=${scr}>${x}</a>`
            }).join("");
    });
});


function reportError() {
    text = editor.getValue();
    if (text.length > 4096) {
      text = ""
    } 
    window.open("https://docs.google.com/forms/d/e/1FAIpQLSdHUV8yFR8TEa4JCMo7KlvVMLsp4ckSf17Ps0RB6kNt71UXEA/viewform?usp=pp_url&entry.495711450=" + encodeURIComponent(text))
}

//     $(document).ready(function () {
//       update(JSON.parse(
//         `
//         { 

// "Status" : "1 Errors",
// "Time" : "2.82 seconds",

// "Errors" : [
// {
//  "line" : 30,
//  "column" : 7,
//  "message" : "Reduction failure",
//  "trace": [
// {
//   "line": 28,
//   "stmt": "while (true)   {",
//   "mover": "R",
//   "heap": "./log/24.18847.png",
//   "justification": { 
//     "preds" : [ "!isLocal(this, tid)","!holds(this, tid)" ],
//     "access" : "this.head"
//       }

// },
// {
//   "line": 28,
//   "stmt": "tmp2 = true;",
//   "mover": "N",
//   "heap": "",
//   "justification": { 
//     "preds" : [ "!isLocal(this, tid)","!holds(this, tid)" ],
//     "access" : "this.head"
//       }

// },
// {
//   "line": 28,
//   "stmt": "call;",
//   "mover": "L",
//   "heap": "",
//   "justification": { 
//     "preds" : [ "!isLocal(this, tid)","!holds(this, tid)" ],
//     "access" : "this.head"
//       },
//   "extra" : "PUSH"
// },
// {
//   "line": 28,
//   "stmt": "retrun;",
//   "mover": "B",
//   "heap": "",
//   "justification": { 
//     "preds" : [ "!isLocal(this, tid)","!holds(this, tid)" ],
//     "access" : "this.head"
//       },
//   "extra" : "POP"
// },
// {
//   "line": 28,
//   "stmt": "if (!tmp2) {",
//   "mover": "L",
//   "heap": "",
//   "justification": { 
//     "preds" : [ "!isLocal(this, tid)","!holds(this, tid)" ],
//     "access" : "this.head"
//       }
// },
// {
//   "line": 30,
//   "stmt": "tmp4 := this.head;",
//   "mover": "E",
//   "heap": "./log/24.18828.png",
//   "justification": { 
//     "preds" : [ "!isLocal(this, tid)","!holds(this, tid)" ],
//     "access" : "this.head"
//       }
// }
// ]
// },


// {
//  "line" : 30,
//  "column" : 7,
//  "message" : "Validity Error",
//  "threads": [
//  {
//     "threads": ["t", "u" ],
//     "stmts" : [ "tmp4 := this.head;", "tmp4 := this.head;" ],
//     "movers": ["E", "E" ],
//     "heap": "./log/24.18828.png",
//     "justifications":
//     [ 
//       { 
//         "preds" : [ "!isLocal(this, tid)","!holds(this, tid)" ],
//         "access" : "this.head"
//       },
//       { 
//         "preds" : [ "!isLocal(this, tid)","!holds(this, tid)" ],
//         "access" : "this.head"
//       }
//     ]
//   }
//  ]
// }
// ],
// "Dummy" : 3 
// } 
// `
//       ))
//     });
