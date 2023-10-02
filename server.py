# Python 3 server example
from http.server import BaseHTTPRequestHandler, HTTPServer, SimpleHTTPRequestHandler
import urllib.parse
import tempfile
import time
import os
import shlex
from subprocess import Popen, PIPE, TimeoutExpired
import json
import sys
import argparse
from concurrent.futures import ThreadPoolExecutor
from socketserver     import ThreadingMixIn
import threading

import os
import signal
import subprocess



verifyTimeout = 90

timeoutError = """
                { 
                    "Status" : "Time or Memory Limit Exceeded",
                    "Errors" : [
                       {
                        "line" : 1,
                        "column" : 1,
                        "message" : "The Anchor Verifier web service limits the time and memory a query may use.  Install Anchor locally if timeouts persist for your programs.  See <a target=\\"_blank\\" href=\\"https://doi.org/10.5281/zenodo.4032624\\">here</a> for details."
                       }
                    ]
                }
                """

class MyServer(SimpleHTTPRequestHandler):

    def log_message(self, format, *args):
        sys.stderr.write("%s - %s - [%s] %s - %s\n" %
                         (self.address_string(),
                          self.headers.get('X-Forwarded-For') if hasattr(self, "headers") else "",
                          self.log_date_time_string(),
                          threading.current_thread().name,
                          format%args))
                        

    def do_GET(self):
        if (self.path == "/examples/"):
            self.send_response(200)
            self.send_header("Content-type", "text/json")
            self.send_header('Access-Control-Allow-Origin', '*')
            self.end_headers()
#            files = [x for x in os.listdir("./examples/") if x.endswith(".anchor") ]
            files = [
                "Stack.anchor",
                "LockFreeStack.anchor",
                "ErrorMessage1.anchor",
                "ErrorMessage2.anchor",
                "ErrorMessage3.anchor",
                "LockFreeQueue.anchor",
                "AtomicInt.anchor",
                "QueueWithAbstraction.anchor"

            ]
            self.wfile.write(bytes(json.dumps(files), "utf-8"))
        else:
            super().do_GET()

    def do_POST(self):
        if self.path != "/verify":
            self.send_response(400)
            self.end_headers()
            return
    
        # print(urllib.parse.parse_qs(self.path))
        content_len = int(self.headers.get('Content-Length'))
        post_body = self.rfile.read(content_len)
        original = post_body.decode('utf-8')

        self.log_message("++++++++++++")
        self.log_message("Thread: " + str(threading.get_ident()))
        self.log_message("============")
        for line in original.split("\n"):
            self.log_message("%s", line)

        with tempfile.TemporaryDirectory() as tmpDir:
            # print('created temporary directory', tmpDir)

            # uncomment to always just use /tmp for debugging...
            #tmpDir = "/tmp"

            initAnchorFile = tmpDir + "/a.anchor"
            finiAnchorFile = tmpDir + "/b.anchor"

            with open(initAnchorFile, "w") as text_file:
                text_file.write(original)

            with open(finiAnchorFile, "w") as text_file:
                with Popen(["cpp", "-traditional-cpp", "-nostdinc", "-C", "-E", "-W", "-P", initAnchorFile], stdout=PIPE, text=True) as proc:
#                with Popen(["gpp", "-C", initAnchorFile], stdout=PIPE, text=True) as proc:
                    x = proc.stdout.read()
                    text_file.write(x)

            args = " ".join([ x[10:] for x in original.split("\n") if x.startswith("///: args") ])

            self.log_message(tmpDir)
 
            process = Popen(shlex.split("./server-anchor " + args + " -logs=" + tmpDir + " " + finiAnchorFile),stdout=PIPE,stderr=PIPE,text=True,preexec_fn=os.setsid)

            self.log_message("------------")
            self.log_message("Start anchor")
            startTime = time.time()
            try:
                (output, err) = process.communicate(timeout=verifyTimeout)
            except:
                try:
                    self.log_message("Exception -- killing verify process")
                    os.killpg(os.getpgid(process.pid), signal.SIGTERM)  # Send the signal to all the process groups
                except:
                    self.log_message("Couldn't kill processes")
                output = timeoutError
            self.log_message("Stop anchor (" + str(time.time() - startTime) + ")")
            self.log_message("Return Code " + str(process.returncode))
            self.log_message("------------")

            foundTimeoutMessage = False
            for data in output.split("\n"):
                self.log_message("%s", (data[:120] + '..') if len(data) > 120 else data)
                if "' timed out after" in data or "Boogie exited with code 1." in data:
                   foundTimeoutMessage = True
            if foundTimeoutMessage:
                output = timeoutError

            if process.returncode != 0:
                output = timeoutError

            self.send_response(200)
            self.send_header("Content-type", "text/json")
            self.send_header('Access-Control-Allow-Origin', '*')
            self.end_headers()

            self.log_message("############")
            self.wfile.write(bytes(output, "utf-8"))
            self.wfile.flush()
            
class PoolMixIn(ThreadingMixIn):
    def process_request(self, request, client_address):
        self.pool.submit(self.process_request_thread, request, client_address)

class PoolHTTPServer(PoolMixIn, HTTPServer):

    pool = ThreadPoolExecutor(max_workers= os.cpu_count() * 2, thread_name_prefix="T")
        

if __name__ == "__main__":       

    os.chdir(os.path.dirname(os.path.abspath(__file__)))

    parser = argparse.ArgumentParser()
    parser.add_argument("-t", "--threads", action="store_true")
    parser.add_argument("port", type=int, default=8080)
    args = parser.parse_args()

    hostName = ""

    if args.threads:
        webServer = PoolHTTPServer((hostName, args.port), MyServer)
        print("Server Multithreaded started http://%s:%s" % (hostName, args.port))
        print("Using %d Threads." % (os.cpu_count() * 2))
    else:
        webServer = HTTPServer((hostName, args.port), MyServer)
        print("Server started http://%s:%s" % (hostName, args.port))

    try:
        webServer.serve_forever()
    except KeyboardInterrupt:
        pass

    webServer.server_close()
    print("Server stopped.")
