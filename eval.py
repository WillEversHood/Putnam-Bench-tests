import os 

def lean_string():
    lean_file = "lean4/src/putnam_1962_a1.lean"

    with open(lean_file, "r", encoding="utf-8") as f:
        lean_code = f.read()

    return lean_code 

if __name__=="__main__":
    print(lean_string())
    