import scala.util.continuations._
import org.scala_lang.virtualized.virtualize
import org.scala_lang.virtualized.SourceContext

import scala.virtualization.lms._
import scala.virtualization.lms.common._
import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable.{Map => MutableMap}
import scala.math._

object lang {

  abstract class Exp
  case class Const(a: Any) extends Exp
  case class Sym(b: Int) extends Exp
  case class Add(a: Exp, b: Exp) extends Exp
  case class Mul(a: Exp, b: Exp) extends Exp
  case class Lam(x: Sym, e: Exp) extends Exp
  case class App(a: Exp, b: Exp) extends Exp
  case class Let(x: Sym, a: Exp, b: Exp) extends Exp
  case class Pair(a: Exp, b: Exp) extends Exp
  case class Fst(a: Exp) extends Exp
  case class Snd(a: Exp) extends Exp
  case class Ref(a: Exp) extends Exp
  case class Deref(a: Exp) extends Exp
  case class Assign(a: Exp, b: Exp) extends Exp
  case class Inl(a: Exp) extends Exp
  case class Inr(a: Exp) extends Exp
  case class Case(a: Exp, y1: Sym, a1: Exp, y2: Sym, a2: Exp) extends Exp

  var counter = -1
  def next = {
    counter += 1
    counter
  }
  def resetCounter = {
    counter = -1
  }
  def sym = {
    Sym(next)
  }

  def trans(e: Exp): Exp @cps[Exp] = e match {
    case Const(a: Float) =>
      Pair(Const(a), Ref(Const(0)))
    case Const(a) => Const(a)
    case Sym(b)   => Sym(b) // no syntactic sugar
    case Add(a, b) =>
      val y1 = sym
      val y2 = sym
      val y3 = sym
      shift { (k: Exp => Exp) => reset{
        Let(y1, trans(a),
        Let(y2, trans(b),
        Let(y3, Pair(Add(Fst(y1), Fst(y2)), Ref(Const(0))),
        Let(Sym(-1), k(y3),
        Let(Sym(-1), Assign(Snd(y1), Add(Deref(Snd(y1)), Deref(Snd(y3)))),
        Assign(Snd(y2), Add(Deref(Snd(y2)), Deref(Snd(y3)))))))))
      }}
    case Mul(a, b) =>
      val y1 = sym
      val y2 = sym
      val y3 = sym
      shift { (k: Exp => Exp) => reset{
        Let(y1, trans(a),
        Let(y2, trans(b),
        Let(y3, Pair(Mul(Fst(y1), Fst(y2)), Ref(Const(0))),
        Let(Sym(-1), k(y3),
        Let(Sym(-1), Assign(Snd(y1), Add(Deref(Snd(y1)), Mul(Deref(Snd(y3)), Fst(y2)))),
        Assign(Snd(y2), Add(Deref(Snd(y2)), Mul(Deref(Snd(y3)), Fst(y1)))))))))
      }}
    case Lam(x, e) =>
      val k = sym
      Lam(x, Lam(k, reset{ App(k, trans(e)) }))

    case App(a, b) => shift { (k: Exp => Exp) => reset{
      val y = sym
      App(App(trans(a), trans(b)), Lam(y, k(y)))
    }}

    case Let(y, a, b) => shift { (k: Exp => Exp) => reset{
      Let(y, trans(a), reset{ k(trans(b)) })
    }}

    case Pair(a, b) => Pair(trans(a), trans(b))
    case Fst(a) => Fst(trans(a))
    case Snd(a) => Snd(trans(a))
    case Ref(a) => Ref(trans(a))
    case Deref(a) => Deref(trans(a))
    case Assign(a, b) => Assign(trans(a), trans(b))
    case Inl(a) => Inl(trans(a))
    case Inr(a) => Inr(trans(a))
    case Case(e, y1, e1, y2, e2) => shift { (k: Exp => Exp) => reset {
      val k1 = sym
      val a = sym
      Let(k1, Lam(a, k(a)),
        Case(trans(e), y1, reset{App(k1, trans(e1))}, y2, reset{App(k1, trans(e2))})
      )
    }}
  }

  def show(e: Exp, indent: String = ""): String = e match {
    case Const(a)     => s"${indent}$a"
    case Sym(a)       => s"${indent}x$a"
    case Add(a, b)    => s"${indent}(${show(a)} + ${show(b)})"
    case Mul(a, b)    => s"${indent}(${show(a)} * ${show(b)})"
    case Lam(x, e)    => s"${indent}(fun (${show(x)}) => ${show(e)})" 
    case App(a, b)    => s"${indent}(@ ${show(a)} ${show(b)})"
    case Let(Sym(-1), a, b) => s"${show(a, indent)};\n${show(b, indent)}"
    case Let(x, a, b) => s"${indent}let ${show(x)} = ${show(a)} in\n${show(b, indent + "  ")}"  
    case Pair(a, b)   => s"${indent}<${show(a)}, ${show(b)}>"
    case Fst(a)       => s"${indent}${show(a)}._1"
    case Snd(a)       => s"${indent}${show(a)}._2"
    case Ref(a)       => s"${indent}(ref ${show(a)})"
    case Deref(a)     => s"${indent}(! ${show(a)})"
    case Assign(a, b) => s"${indent}${show(a)} := ${show(b)}"
    case Inl(a)       => s"${indent}(inl ${show(a)})"
    case Inr(a)       => s"${indent}(inr ${show(a)})"
    case Case(e, y1, e1, y2, e2) =>
      s"${indent}case ${show(e)} of ${show(y1)} ${show(e1)} or ${show(y2)} ${show(e2)}"
  }
  def showOut(e: Exp): Unit = println(show(e, "  "))

  def test(name: String)(e: => Exp) = {
    resetCounter
    println(s"$name before transformation")
    showOut(e)
    println(s"$name after transformation")
    val x = sym
    val xhat = sym
    val z = sym    
    showOut{
      Lam(x,
        Let(xhat, Pair(x, Ref(Const(0.0f))),
          Let(Sym(-1), App(App(reset(trans(e)), xhat), Lam(z, Assign(Snd(z), Const(1.0f)))),
            Deref(Snd(xhat))
          )
        )
      )
    }
  }

  def main(args: Array[String]) {
    test("term0"){
      val x = sym
      Lam(x, x)
    }
    test("term1"){
      val x = sym
      Lam(x, Add(x, Const(1.0f)))
    }
    test("term2"){
      val x = sym
      Lam(x, Add(x, x))
    }
    test("term3"){
      val x = sym
      Lam(x, Add(Add(x, Const(2.0f)), x))
    }
    test("term4"){
      val x = sym
      val y = sym
      Lam(x, App(Lam(y, Add(y, y)), x))
    }
    test("term5"){
      val x = sym
      val y = sym
      Lam(x, Let(y, Const(1.0f), Add(y, x)))
    }
    test("loop"){
      val l = sym
      val f0 = sym
      val f = sym
      val ll = sym
      val ac = sym
      val x = sym
      val x0 = sym
      val y1 = sym
      val y2 = sym
      Lam(x, Let(l, Inr(Inr(Inl(Const(())))), 
        Let(f0, Lam(f, Lam(ll, Lam(ac,
          Case(ll, y1, ac, y2, App(App(App(f, f), y2), Mul(x, ac)))))),
          App(App(App(f0, f0), l), Const(1.0f)))))
    }
    test("list"){
      val x = sym
      val l = sym
      val f0 = sym
      val f = sym
      val ll = sym
      val y1 = sym
      val y2 = sym
      Lam(x, Let(l, Inr(Pair(Const(5.0f), Inr(Pair(Const(6.0f), Inr(Const(())))))),
        Let(f0, Lam(f, Lam(ll, Case(ll, y1, x, y2, Mul(Fst(y2), App(App(f, f), Snd(y2)))))),
          App(App(f0, f0), l))))
    }
    test("tree"){
      val x = sym
      val t = sym
      val f0 = sym
      val f = sym
      val tt = sym
      val y1 = sym
      val y2 = sym
      Lam(x, Let(t, Inr(Pair(Const(5.0f), Pair(Inl(Const(())), Inl(Const(()))))),
        Let(f0, Lam(f, Lam(tt, Case(tt, y1, x, y2, Add(Add(Fst(y2), App(App(f, f), Fst(Snd(y2)))), App(App(f, f), Snd(Snd(y2))))))),
          App(App(f0, f0), t))))
    }
  }
}

