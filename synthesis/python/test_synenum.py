import unittest
import synenum as e

class TestExprsMethods(unittest.TestCase):
  def test_expr_gt1(self):
    t1 = e.Expr("(+ (* x z) (* y z))", e.build_histo_from_list(["add", "mul"]), "add")
    t2 = e.Expr("(* z (+ x y))", e.build_histo_from_list(["add","mul"]), "mul")
    self.assertTrue(e.expr_gt(t1, t2))

  def test_expr_gt2(self):
    t1 = e.Expr("(< (ite x y z) z)", e.build_histo_from_list(["select","lt"]), "lt")
    t2 = e.Expr("(ite x (< y z) false)", e.build_histo_from_list(["select","lt"]), "select")
    self.assertTrue(e.expr_gt(t1, t2))

  def test_expr_gt3(self):
    t1 = e.Expr("(ite x (< y w) (< z w))", e.build_histo_from_list(["select","lt","lt"]), "select")
    t2 = e.Expr("(< (ite x y z) w)", e.build_histo_from_list(["select","lt"]), "lt")
    self.assertTrue(e.expr_gt(t1, t2))

  def test_add_histos(self):
    h1 = e.build_histo_from_list(["select","lt","lt"])
    h2 = e.build_histo_from_list(["select","lt"])
    h3 = e.add_histos(h1, h2)
    self.assertEqual(h3["select"], 2)
    self.assertEqual(h3["lt"], 3)

if __name__ == '__main__':
    unittest.main()