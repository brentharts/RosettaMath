# lean4.py - Version 0.1: The Micro-Kernel

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
    """Dependent function type: \forall (x : A), B"""
    def __init__(self, var_name, var_type, body):
        self.var_name = var_name
        self.var_type = var_type
        self.body = body
    def __str__(self):
        return f"(∀ {self.var_name} : {self.var_type}, {self.body})"

class Lambda(Expr):
    """Anonymous function: \x : A => body"""
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
