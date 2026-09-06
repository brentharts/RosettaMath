# lean4.py - Version 0.2: The Micro-Kernel
import ast
import inspect

__doc__ = r'''
The lean4.py Micro-Kernel:
a mathematical engine capable of understanding that a function takes an argument of type $A$ and returns something of type $B$. This is the Calculus of Constructions (CoC), the foundation of Lean, Coq, and dependent type theory.  Inspired by:
 https://github.com/leanprover/lean4
 https://xenaproject.wordpress.com/2019/02/11/lean-in-latex/

LaTeX Native:
By treating LaTeX not as an output format (like the Xena project did), but as an input language, you are essentially creating a literate programming environment where mathematics and Python code live together seamlessly.

Modern Lean 4 is a massive, heavily engineered beast:
While its scale is necessary for verifying complex modern mathematics (like the Liquid Tensor Experiment), it is fundamentally overkill because our goal is just to have a lightweight, hackable engine to play with dependent types, Python code verification, and LaTeX formatting.

The Xena Project blog post (above) highlights a crucial idea: making formal proofs readable to humans by bridging Lean and LaTeX/HTML. Patrick Massot’s format_lean tool took Lean code and rendered the "tactic state" (the step-by-step logic) into a beautiful, mathematician-friendly format.

We propose flipping that bridge: Using a subset of LaTeX as the input language to write proofs about Python code, powered by a minimalist Python-based theorem prover.

'''

class Expr:
    """Base class for all logical expressions."""
    def __eq__(self, other):
        # We need equality to compare types (e.g., does expected type match actual type?)
        return str(self) == str(other)

class Universe(Expr):
    """Sorts/Universes: Prop (0), Type (1), Type 1 (2), etc."""
    def __init__(self, level=0):
        self.level = level
    def __str__(self):
        return "Prop" if self.level == 0 else f"Type {self.level - 1}"

class Var(Expr):
    """A variable like 'x' or 'Nat'."""
    def __init__(self, name):
        self.name = name
    def __str__(self):
        return self.name

class Pi(Expr):
    """Dependent function type: \\forall (x : A), B"""
    def __init__(self, var_name, var_type, body):
        self.var_name = var_name
        self.var_type = var_type
        self.body = body
    def __str__(self):
        return f"(∀ {self.var_name} : {self.var_type}, {self.body})"

class Lambda(Expr):
    """Anonymous function: \\x : A => body"""
    def __init__(self, var_name, var_type, body):
        self.var_name = var_name
        self.var_type = var_type
        self.body = body
    def __str__(self):
        return f"(λ {self.var_name} : {self.var_type} ⇒ {self.body})"

class App(Expr):
    """Function application: f(x)"""
    def __init__(self, func, arg):
        self.func = func
        self.arg = arg
    def __str__(self):
        return f"{self.func}({self.arg})"

# --- Core Engine Operations ---

def substitute(expr: Expr, var_name: str, replacement: Expr) -> Expr:
    """Replaces all instances of 'var_name' in 'expr' with 'replacement'."""
    if isinstance(expr, Universe):
        return expr
    elif isinstance(expr, Var):
        return replacement if expr.name == var_name else expr
    elif isinstance(expr, App):
        return App(substitute(expr.func, var_name, replacement), 
                   substitute(expr.arg, var_name, replacement))
    elif isinstance(expr, (Pi, Lambda)):
        # If the bound variable shadows the one we are replacing, stop substituting.
        if expr.var_name == var_name:
            return expr
        # Otherwise, substitute inside the type and the body.
        new_type = substitute(expr.var_type, var_name, replacement)
        new_body = substitute(expr.body, var_name, replacement)
        return type(expr)(expr.var_name, new_type, new_body)
    return expr

def normalize(expr: Expr) -> Expr:
    """Evaluates the expression (Beta-Reduction)."""
    if isinstance(expr, App):
        func_eval = normalize(expr.func)
        arg_eval = normalize(expr.arg)
        # If we have (λx:A. body)(arg), beta-reduce it!
        if isinstance(func_eval, Lambda):
            reduced = substitute(func_eval.body, func_eval.var_name, arg_eval)
            return normalize(reduced)
        return App(func_eval, arg_eval)
    return expr

def type_check(ctx: dict, expr: Expr) -> Expr:
    """
    Returns the Type of the expression, or raises an Exception if invalid.
    This is the core 'Proof Checker' logic.
    """
    if isinstance(expr, Universe):
        return Universe(expr.level + 1)
    
    elif isinstance(expr, Var):
        if expr.name not in ctx:
            raise TypeError(f"Unknown identifier: {expr.name}")
        return ctx[expr.name]
    
    elif isinstance(expr, Lambda):
        # 1. Type check the domain (A)
        type_check(ctx, expr.var_type)
        # 2. Add x : A to the context
        new_ctx = ctx.copy()
        new_ctx[expr.var_name] = expr.var_type
        # 3. Type check the body
        body_type = type_check(new_ctx, expr.body)
        # 4. The type of a Lambda is a Pi type
        return Pi(expr.var_name, expr.var_type, body_type)
        
    elif isinstance(expr, App):
        # 1. Get the type of the function
        func_type = normalize(type_check(ctx, expr.func))
        if not isinstance(func_type, Pi):
            raise TypeError(f"Expected a function, got {func_type}")
        # 2. Get the type of the argument
        arg_type = type_check(ctx, expr.arg)
        # 3. Check if the argument type matches what the function expects
        if normalize(func_type.var_type) != normalize(arg_type):
            raise TypeError(f"Type mismatch: expected {func_type.var_type}, got {arg_type}")
        # 4. The return type is the body of the Pi type, with the argument substituted in
        return normalize(substitute(func_type.body, func_type.var_name, expr.arg))

    raise TypeError(f"Cannot typecheck: {expr}")



# --- Python AST to Lean Kernel Bridge ---

class PythonToLean(ast.NodeVisitor):
    """Compiles Python AST nodes into Lean Kernel Expressions."""
    
    def visit_FunctionDef(self, node: ast.FunctionDef) -> Expr:
        # For our micro-kernel, we assume the function body is a single return statement
        if len(node.body) != 1 or not isinstance(node.body[0], ast.Return):
            raise NotImplementedError("Currently only single 'return' statements are supported.")
        
        # Parse the return value
        body_expr = self.visit(node.body[0].value)
        
        # Build the lambdas from the arguments (right to left)
        expr = body_expr
        for arg in reversed(node.args.args):
            arg_name = arg.arg
            # If there's a type hint (e.g., x: Nat), use it. Otherwise default to a base Type.
            if arg.annotation and isinstance(arg.annotation, ast.Name):
                arg_type = Var(arg.annotation.id)
            else:
                arg_type = Universe(0) 
            
            expr = Lambda(arg_name, arg_type, expr)
            
        return expr

    def visit_Name(self, node: ast.Name) -> Expr:
        """Variables like 'x' become Var('x')"""
        return Var(node.id)

    def generic_visit(self, node):
        raise SyntaxError(f"Unsupported Python syntax for theorem prover: {type(node).__name__}")

def compile_python_to_lean(func) -> Expr:
    """Takes a Python function and returns its Lean Kernel representation."""
    source = inspect.getsource(func)
    # Dedent in case the function is defined inside another block
    import textwrap
    source = textwrap.dedent(source)
    
    tree = ast.parse(source)
    # The root is a Module, the first body item is the FunctionDef
    translator = PythonToLean()
    return translator.visit(tree.body[0])

# --- The Decorator ---

# A global logical environment for our theorems
GLOBAL_ENV = {
    "Nat": Universe(0),
    "Prop": Universe(0)
}

def theorem(latex_statement: str):
    """
    Decorator to verify a Python function against a logical statement.
    """
    def decorator(func):
        print(f"\n--- Checking Theorem: {func.__name__} ---")
        print(f"LaTeX Statement: {latex_statement}")
        
        try:
            # 1. Compile Python to Lean AST
            lean_expr = compile_python_to_lean(func)
            print(f"Compiled Kernel Expr: {lean_expr}")
            
            # 2. Type-check the expression
            expr_type = type_check(GLOBAL_ENV, lean_expr)
            print(f"Inferred Type: {expr_type}")
            
            # (Future step: verify the inferred type matches the latex_statement)
            
            print("Status: VALID (Type Checks)")
        except Exception as e:
            print(f"Status: FAILED - {e}")
            
        return func
    return decorator

# --- Test the Engine ---
if __name__ == "__main__":
    print("--- Lean4 Micro-Kernel Initialized ---")
    
    # Let's define an environment with some base types
    environment = {
        "Nat": Universe(0),               # Nat is a Type
        "x": Var("Nat"),                  # x is a Nat
        "String": Universe(0)             # String is a Type
    }

    # The Identity Function: f(x) = x
    # In Lean: fun (T : Type) (a : T) => a
    id_func = Lambda("T", Universe(0), 
                Lambda("a", Var("T"), 
                    Var("a")))

    print(f"Identity Function: {id_func}")
    id_type = type_check(environment, id_func)
    print(f"Type of Identity Function: {id_type}")

    # Apply the Identity function to the Type 'Nat', and then to the variable 'x'
    # id(Nat)(x) -> should evaluate to x, and its type should be Nat
    app1 = App(id_func, Var("Nat"))
    app2 = App(app1, Var("x"))
    
    print(f"\nExpression: {app2}")
    print(f"Evaluates to: {normalize(app2)}")
    print(f"Typechecks as: {type_check(environment, app2)}")
    
    print("\n\n=== Testing the Python Bridge ===")

    # We use a dummy LaTeX string for now until we connect the LaTeX parser
    @theorem(r"\forall x \in \text{Nat}, x = x")
    def identity_function(x: 'Nat'):
        return x

    @theorem(r"\text{Shows that returning an undeclared variable fails}")
    def faulty_function(x: 'Nat'):
        return y
