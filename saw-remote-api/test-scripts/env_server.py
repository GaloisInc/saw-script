import os
import saw as saw
import saw.connection as conn

def env_connect():
    server = os.environ.get('SAW_SERVER')
    if not server:
        server = "cabal new-exec --verbose=0 saw-remote-api socket"
    print("Running: " + server)
    return conn.connect(server)

def env_connect_global():
    server = os.environ.get('SAW_SERVER')
    if not server:
        server = "cabal new-exec --verbose=0 saw-remote-api socket"
    print("Running: " + server)
    saw.connect(server)
