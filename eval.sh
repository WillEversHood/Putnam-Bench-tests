#!/bin/bash
cd ~/Documents/GitHub/Putnam-Bench-tests
if [ "$1" = "light" ]; then
    dir="src_light"
else
    dir="src"
fi

# Create an array of filenames
mapfile -t files < <(find "$dir" -maxdepth 1 -type f -printf "%f\n")


correct=0
wrong=0
echo "number of files: ${#files[@]}"
for name in "${files[@]}"; do
    cd ~/Documents/GitHub/Putnam-Bench-tests
    lean_code=$(python3 eval.py $name)
    # run crewai agent with lean_code as the context
    cd ~/Documents/GitHub/Putnam-Bench-tests/lean4_formalizer
    crewai install
    crewai run "$lean_code"
    sed '1d;$d' lean_log.txt > lean_test.txt
    mv lean_test.txt ../test_space/lean_test.lean
    cd ~/Documents/GitHub/Putnam-Bench-tests/test_space
    if lean lean_test.lean > /dev/null 2>&1; then
        echo "Proof is correct ✅"
        let correct=correct+1
    else
        echo "Proof is incorrect ❌"
        let wrong=wrong+1
    fi
done

