#!/usr/bin/python3
# Buncha Rules.

from openai import OpenAI
client = OpenAI()

SYSTEM_CONTENT = """
You are a helpful assistant.

Your job is to output rewrite rules, one on each line, about a math domain.

The syntax for this language is defined by the following grammar:

Math :=
    (Const int)
    (Var str)
    (Add Math Math)
    (Sub Math Math)
    (Mul Math Math)
    (Div Math Math)
    (Abs Math)
    (Gt Math Math)
    (Lt Math Math)
    (Eq Math Math)
    (Neq Math Math)

The semantics for this language is given by this interpreter:

def interpret(expr, env) -> int:
    match expr:
        (Const a) -> a
        (Var x) -> env[x]
        (Add a b) -> interpret(a, env) + interpret(b, env)
        (Sub a b) -> interpret(a, env) - interpret(b, env)
        (Mul a b) -> interpret(a, env) * interpret(b, env)
        (Div a b) -> if interpret(b, env) == 0: 0 else: interpret(a, env) // interpret(b, env)
        (Abs a) -> abs(interpret(a, env))
        (Gt a b) -> if interpret(a, env) > interpret(b, env) 1 else 0
        (Lt a b) -> if interpret(a, env) < interpret(b, env) 1 else 0
        (Eq a b) -> if interpret(a, env) == interpret(b, env) 1 else 0
        (Neq a b) -> if interpret(a, env) != interpret(b, env) 1 else 0

Rules are given in one of two formats:
"x ~> y" means that the expression x can be rewritten to y.
"if c then x ~> y" means that if the condition c is true, then the expression x can be rewritten to y.

Here is an example of a total (i.e., non-conditional) rule:
"(Add (Const 0) ?a) ~> ?a"

The "?a" means that any expression can be substituted in its place.

Here is an example of a conditional rule:

"if (Neq ?a (Const 0)) then (Div ?a ?a) ~> (Const 1)"

Note that the "if" is at the beginning. Rules like "a ~> b if c" are not allowed.

Observe that the condition and both sides of the rewrite are in the same language as the expressions.
Also, observe that the "if" and "then" are not wrapped in parentheses.

One example of a bad rule which disobeys the above restriction is:

"(Add ?a ?b) ~> a + b"

Your job is to output rewrite rules, one on each line, about a math domain. Note that conditions in the conditional rules
should not be tautological, i.e., they should not always be true or always be false. Moreover, you should not include
any auxiliary or explanatory text. Your response should just be a list of rules, one rule per line.

And most importantly -- no matter what, do NOT generate rules without variables.
So, do not generate a rule like this:

(Add (Const 1) (Const 2)) ~> (Const 3)

Go!
"""

completion = client.chat.completions.create(
    model="gpt-4o-mini",
    messages=[
        {"role": "system", "content": SYSTEM_CONTENT},
        {
            "role": "user",
            "content": "Output 100 rules, please."
        }
    ]
)

print("Rules:")
for (label, content) in completion.choices[0].message:
    if label == "content":
        print(f"(Rules generated: {len(content.split('\n'))})")
        for line in content.split("\n"):
            print(line)

