import os 
import sys
def lean_string():
    lean_file = "src/"
    lean_file = lean_file + sys.argv[1]

    with open(lean_file, "r", encoding="utf-8") as f:
        lean_code = f.read()

    return lean_code 

if __name__=="__main__":
    print(lean_string())
    