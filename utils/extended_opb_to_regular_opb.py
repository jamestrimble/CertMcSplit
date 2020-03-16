from collections import defaultdict
import sys

def incrementer():
    val = 0
    def fun():
        nonlocal val
        val += 1
        return "x" + str(val)
    return fun

old_to_new_var_name = defaultdict(incrementer())

for line_num, line in enumerate(sys.stdin.readlines()):
    tokens = line.strip().split()
    if not tokens:
        continue
    if tokens[0][0] == "*" and line_num != 0:
        continue
    for i, token in enumerate(tokens):
        if token.startswith("~x"):
            tokens[i] = "~" + old_to_new_var_name[token[1:]]
        elif token.startswith("x"):
            tokens[i] = old_to_new_var_name[token]
    print(" ".join(tokens))
