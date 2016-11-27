# submit.py (client)
#
# (c) 2015 George Wong
#

from __future__ import print_function
import subprocess
import socket
import sys

####

SERVER_ADDR = 'cso15.jinyangli.com' 
SERVER_PORT = 5000
VERBOSE = False


####


def run_test(name, data):
    return subprocess.check_output(["./" + name, str(data)])


if __name__ == "__main__":

    STUDENT = {
        "name": "",
        "netid": "",
        "nid": "",
        "cc": "",
        "full": ""
    }

    print("")

    ## Ensure we have a meaningful program to run
    if len(sys.argv) < 2:
        print("Please run this program with the proper arguments:")
        print("  python submit.py <sample>\n")
        exit(-3)

    ## Get the student info
    try:
        fp = open("my.info", "r")
        for line in fp:
            STUDENT["full"] += line
            if line.strip()[:5].lower() == "name:":
                STUDENT["name"] = line.strip()[5:].strip()
            elif line.strip()[:7].lower() == "net id:":
                STUDENT["netid"] = line.strip()[7:].strip()
            elif line.strip()[:11].lower() == "nyu id(n#):":
                STUDENT["nid"] = line.strip()[11:].strip()
            elif line.strip()[:18].lower() == "confirmation code:":
                STUDENT["cc"] = line.strip()[18:].strip()
        fp.close()
    except:
        print("Unable to open my.info file. Quitting!\n")
        exit(-1)
    # Validate
    valid = 1
    if len(STUDENT["name"]) < 1:
        valid = 0
        print("No name found")
    if len(STUDENT["netid"]) < 1:
        valid = 0
        print("No net id found")
    if len(STUDENT["nid"]) < 1:
        valid = 0
        print("No N# found")
    if len(STUDENT["cc"]) < 1:
        print("No confirmation code found")
        valid = 0
    if valid == 0:
        print(" + Please check your my.info file!\n")
        exit(-5)

    ## Attempt to establish connection with server
    print("Waiting on free connection...")
    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    # s.settimeout(10.0)
    s.connect((SERVER_ADDR, SERVER_PORT))
    s.send("HELO")
    s.recv(64)
    s.send(STUDENT["name"])
    s.recv(64)
    s.send(STUDENT["netid"])
    s.recv(64)
    s.send(STUDENT["nid"])
    s.recv(64)
    s.send(STUDENT["cc"])
    r = s.recv(1024)
    if r != "GOOD":
        print("Server does not like your credentials. Please")
        print("verify your information and try again.\n")
        exit(-2)
    s.send(STUDENT["full"])
    s.send(sys.argv[1])
    if s.recv(1024) != "ACK":
        print("Bad test name. Please ensure you are following the")
        print("correct naming convention!\n")
        exit(-3)

    # Now send mm.c to the server
    with (open("mm.c", "rb")) as file:
        print("Sending mm.c to server")
        for line in file:
            # print("Sending data: " + line)
            s.send(line)
            s.recv(64)
    print("File finished sending")
    s.send("FIN")
    s.recv(64)
    r = s.recv(1024)

    if r != "FACK":
        print("Server did not receive mm.c")
        exit(-4)
    else:
        print("Server received mm.c")

    s.send("ACK")

    print("Waiting for server to run your code...")

    r = s.recv(1024)
    if (r == "ERRORS"):
        print("Your malloc did not work (failed to compile, didn't pass all 10 tests, or something else)")
    else:
        print(r)

    # Run tests
    # tests_passed = 0
    # ntests = int(s.recv(1024))
    # if VERBOSE: print("Beginning " + str(ntests) + " tests")
    # for i in range(ntests):
    #
    #     print('Running  {0:5.1f}%'.format(100. * i / ntests), end='\r')
    #     sys.stdout.flush()
    #
    #     arg = int(s.recv(1024))
    #     out = run_test(sys.argv[1], arg)
    #     s.send(out)
    #     valid = s.recv(1024)
    #     if valid == "valid": tests_passed += 1
    #
    # print('Running  {0:5.1f}%'.format(100.))
    ## Notify submitter of result
    s.close()
    # print('Tests passed: {0:d} of {1:d}\n'.format(tests_passed, ntests))