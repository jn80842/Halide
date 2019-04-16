import subprocess, time

ops_order = ['ramp', 'broadcast', 'select', 'div', 'mul', 'mod', 'sub', 'add', 'maxmin', 'not', 'or', 'and', 'lt', 'eq']
reverse_ops_lookup = {'ramp':1, 'broadcast':2, 'select':3, 'div':4, 'mul':5, 'mod':6, 'sub':7, 'add':8, 'maxmin':9, 'not':10, 'or':11, 'and':12, 'lt':13, 'eq':14}

def get_empty_histo():
  return {'ramp':0, 'broadcast':0, 'select':0, 'div':0, 'mul':0, 'mod':0, 'sub':0, 'add':0, 'maxmin':0, 'not':0, 'or':0, 'and':0, 'lt':0, 'eq':0}

def build_histo_from_list(l):
  h = get_empty_histo()
  for i in range(len(l)):
    h[l[i]] += 1
  return h

def expr_gt(e1, e2):
  if e1.histo == e2.histo:
    return reverse_ops_lookup[e1.root] > reverse_ops_lookup[e2.root]
  else:
    for i in range(len(ops_order)):
      if e1.histo[ops_order[i]] != e2.histo[ops_order[i]]:
        return e1.histo[ops_order[i]] > e2.histo[ops_order[i]]
    return False

def expr_cmp(e1, e2):
  if e1.histo == e2.histo and e1.root == e2.root:
    return 0
  elif expr_gt(e1, e2):
    return 1
  else:
    return -1

def add_histos(h1, h2):
  new_histo = get_empty_histo()
  for i in range(len(ops_order)):
    new_histo[ops_order[i]] = h1[ops_order[i]] + h2[ops_order[i]]
  return new_histo

class Expr:
  def __init__(self,expr_str,histo,root):
    self.expr_str = expr_str
    self.histo = histo
    self.root = root
  def __str__(self):
    return self.expr_str
  def __eq__(self, other):
    if isinstance(other, Expr):
      return self.expr_str == other.expr_str
    else:
      return NotImplemented
  def __ne__(self, other):
    if isinstance(other, Expr):
      return self.expr_str != other.expr_str
    else:
      return NotImplemented

class Variable:
  def __init__(self, tname):
    self.tname = tname
  def __str__(self):
    return self.expr_str

# sample expression: (select((0 < a), min((z*2), (w + 18)), (z*2)) <= (z*2))
# !((z*2) < (select((0<a),min((z*2), (w + 18)), (z*2)))
sample = Expr("(not (< (* z 2) (ite (< 0 x) (min (* z 2) (+ y 18)) (* z 2)))",build_histo_from_list(["not","lt","mul","select","lt","maxmin","mul","add","mul"]),"not")

# rule found manually from above expression
lhs = Expr("(< z (ite x y z))",build_histo_from_list(["lt","select"]),"lt")
rhs = Expr("(and x (< z y))",build_histo_from_list(["and","lt"]),"and")

def make_base_variable(tname):
  return Expr(tname, get_empty_histo(), "")

def make_ramp(t1, t2):
  h = add_histos(t1.histo, t2.histo)
  h["ramp"] += 1
  return Expr("(+ {} (* {} (- lanes 1)))".format(t1, t2), h, "ramp")

def make_broadcast(t):
  h = add_histos(get_empty_histo(), t.histo)
  h["broadcast"] += 1
  return Expr(t.expr_str, h, "broadcast")

def make_select(t1, t2, t3):
  h = add_histos(add_histos(t1.histo,t2.histo),t3.histo)
  h['select'] += 1
  return Expr("(ite {} {} {})".format(t1, t2, t3), h, "select")

def make_div(t1, t2):
  h = add_histos(t1.histo,t2.histo)
  h["div"] += 1
  return Expr("(div {} {})".format(t1, t2), h, "div")

def make_mul(t1, t2):
  h = add_histos(t1.histo,t2.histo)
  h["mul"] += 1
  return Expr("(* {} {})".format(t1, t2), h, "mul")

def make_mod(t1, t2):
  h = add_histos(t1.histo,t2.histo)
  h["mod"] += 1
  return Expr("(mod {} {})".format(t1, t2), h, "mod")

def make_sub(t1, t2):
  h = add_histos(t1.histo,t2.histo)
  h["sub"] += 1
  return Expr("(- {} {})".format(t1, t2), h, "sub")

def make_negate(t):
  h = add_histos(get_empty_histo(), t.histo)
  h["sub"] += 1
  return Expr("(- {})".format(t), h, "sub")

def make_add(t1, t2):
  h = add_histos(t1.histo, t2.histo)
  h["add"] += 1
  return Expr("(+ {} {})".format(t1, t2), h, "add")

def make_max(t1, t2):
  h = add_histos(t1.histo, t2.histo)
  h["maxmin"] += 1
  return Expr("(max {} {})".format(t1, t2), h, "maxmin")

def make_min(t1, t2):
  h = add_histos(t1.histo, t2.histo)
  h["maxmin"] += 1
  return Expr("(min {} {})".format(t1, t2), h, "maxmin")

def make_not(t):
  h = add_histos(get_empty_histo(), t.histo)
  h["not"] += 1
  return Expr("(not {})".format(t), h, "not")

def make_or(t1, t2):
  h = add_histos(t1.histo, t2.histo)
  h["or"] += 1
  return Expr("(or {} {})".format(t1, t2), h, "or")

def make_and(t1, t2):
  h = add_histos(t1.histo, t2.histo)
  h["and"] += 1
  return Expr("(and {} {})".format(t1, t2), h, "and")

def make_lt(t1, t2):
  h = add_histos(t1.histo, t2.histo)
  h["lt"] += 1
  return Expr("(< {} {})".format(t1, t2), h, "lt")

def make_eq(t1, t2):
  h = add_histos(t1.histo, t2.histo)
  h["eq"] += 1
  return Expr("(= {} {})".format(t1, t2), h, "eq")

def arity1(f, inputs):
  new_exprs = []
  for i in inputs:
    new_exprs.append(f(i))
  return new_exprs

def arity2(f, inputs1, inputs2):
  new_exprs = []
  for i in range(len(inputs1)):
    for j in range(len(inputs2)):
      new_exprs.append(f(inputs1[i], inputs2[j]))
  return new_exprs

def comm_arity2(f, inputs):
  new_exprs = []
  for i in range(len(inputs)):
    for j in range(i+1):
      new_exprs.append(f(inputs[i], inputs[j]))
  return new_exprs

def arity3(f, inputs1, inputs2, inputs3):
  new_exprs = []
  for i in range(len(inputs1)):
    for j in range(len(inputs2)):
      for k in range(len(inputs3)):
        new_exprs.append(f(inputs1[i], inputs2[j], inputs3[k]))
  return new_exprs

# returns ints: select, div, mul, mod, sub, negate, add, max, min
# returns 7 * (int length ^ 2) + (int length ^ 3) + (int length)
def int_next_round(int_terms, bool_terms):
  next_round_terms = []
  if len(bool_terms) > 0:
    next_round_terms += arity3(make_select, bool_terms, int_terms, int_terms)
  next_round_terms += arity2(make_div, int_terms, int_terms)
  next_round_terms += comm_arity2(make_mul, int_terms)
  next_round_terms += arity2(make_mod, int_terms, int_terms)
  next_round_terms += arity2(make_sub, int_terms, int_terms)
  next_round_terms += arity1(make_negate, int_terms)
  next_round_terms += comm_arity2(make_add, int_terms)
  next_round_terms += comm_arity2(make_max, int_terms)
  next_round_terms += comm_arity2(make_min, int_terms)
  return next_round_terms

# returns bools: select, not, or, and, lt, eq
# returns 2 * (bool length ^ 2) + (bool length) + (bool length ^ 3) + 2 * (int length ^ 2)
def bool_next_round(int_terms, bool_terms):
  next_round_terms = []
  if len(bool_terms) > 0:
    next_round_terms += arity3(make_select, bool_terms, bool_terms, bool_terms)
    next_round_terms += arity1(make_not, bool_terms)
    next_round_terms += comm_arity2(make_or, bool_terms)
    next_round_terms += comm_arity2(make_and, bool_terms)
  if len(int_terms) > 0:
    next_round_terms += arity2(make_lt, int_terms, int_terms)
    next_round_terms += comm_arity2(make_eq, int_terms)
  return next_round_terms

def get_smt2_query(expr1, expr2, int_vars, bool_vars):
  int_declarations = ["(declare-const {} Int) ".format(i) for i in int_vars]
  bool_declarations = ["(declare-const {} Bool) ".format(b) for b in bool_vars]
  min_fun = "(define-fun min ((x Int) (y Int)) Int  (if (< x y) x y)) "
  max_fun = "(define-fun max ((x Int) (y Int)) Int  (if (< x y) y x)) "
  decl_lanes = "(declare-const lanes Int) "
  assert_lanes = "(assert (> lanes 1)) "
  boilerplate = min_fun + max_fun + decl_lanes + assert_lanes
  assertion = "(assert (not (= {} {}))) ".format(expr1, expr2)
  return "".join(int_declarations) + "".join(bool_declarations) + boilerplate + assertion + "(check-sat) " + "(get-model)"

def call_z3(expr1, expr2, int_vars, bool_vars):
  q = get_smt2_query(expr1, expr2, int_vars, bool_vars)
  p = subprocess.Popen("echo '" + q + "' | z3 -smt2 -in -T:60", stdout=subprocess.PIPE, shell=True)
  p_stdout = p.communicate()[0]
  if "unsat" in p_stdout:
    return "expressions are equivalent!"
  elif "unknown" in p_stdout:
    return "not known if expressions are equivalent or not"
  else:
    return "expressions are not equivalent"

def staged_example():
  start = time.time()
  verified_count = 0
  int_vars = [Expr("y",get_empty_histo(),""), Expr("z",get_empty_histo(),"")]
  bool_vars = [Expr("x",get_empty_histo(),"")]
  bool_consts = [Expr("true", get_empty_histo(), ""), Expr("false", get_empty_histo(), "")]
  inr1 = int_next_round(int_vars, bool_vars + bool_consts)
  bnr1 = bool_next_round(int_vars, bool_vars + bool_consts)
  inr2 = int_next_round(int_vars + inr1, bool_vars + bool_consts + bnr1)
  bnr2 = bool_next_round(int_vars + inr1, bool_vars + bool_consts + bnr1)
  candidates = []
  for t in bnr1 + bnr2:
    if expr_gt(lhs, t):
      verified_count += 1
      output = call_z3(lhs, t, int_vars, bool_vars)
      if output == "expressions are equivalent!":
        print("Candidate rule: {} ==> {}".format(lhs, t))
        candidates.append(t)
  end = time.time()
  print("Called z3 on {} candidate RHS".format(verified_count))
  smallest = sorted(candidates, cmp=expr_cmp)
  print("Smallest candidate RHS: {}".format(smallest[0]))
  print(end - start)

def find_all_true_depth2():
  true_expr = make_base_variable("false")
  bool_consts = [Expr("true", get_empty_histo(), ""), Expr("false", get_empty_histo(), "")]
  int_vars = [make_base_variable("i1"),make_base_variable("i2"),make_base_variable("i3")]
  bool_vars = [make_base_variable("b1"),make_base_variable("b2"),make_base_variable("b3")]
  inr1 = int_next_round(int_vars, bool_vars + bool_consts)
  bnr1 = bool_next_round(int_vars, bool_vars + bool_consts)
  bnr2 = bool_next_round(int_vars + inr1, bool_vars + bool_consts + bnr1)
  bnr1_true = []
  for t in bnr1: # + bnr2:
    output = call_z3(t, true_expr, int_vars, bool_vars)
    if output == "expressions are equivalent!":
      bnr1_true.append(t)

def find_all_false_depth2():
  false_expr = make_base_variable("false")
  bool_consts = [Expr("true", get_empty_histo(), ""), Expr("false", get_empty_histo(), "")]
  int_vars = [make_base_variable("i1"),make_base_variable("i2"),make_base_variable("i3")]
  bool_vars = [make_base_variable("b1"),make_base_variable("b2"),make_base_variable("b3")]
  inr1 = int_next_round(int_vars, bool_vars + bool_consts)
  bnr1 = bool_next_round(int_vars, bool_vars + bool_consts)
  bnr2 = bool_next_round(int_vars + inr1, bool_vars + bool_consts + bnr1)
  bnr1_false = []
  for t in bnr1: # + bnr2:
    output = call_z3(t, false_expr, int_vars, bool_vars)
    if output == "expressions are equivalent!":
      bnr1_false.append(t)
  bnr2 = bool_next_round(int_vars + inr1, bool_vars + bool_consts + (list(set(bnr1) - set(bnr1_false))))
  for t in bnr2:
    output = call_z3(t, false_expr, int_vars, bool_vars)
    if output == "expressions are equivalent!":
      print("Candidate rule: {} ==> {}".format(t, false_expr))


