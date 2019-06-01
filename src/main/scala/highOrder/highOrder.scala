import scala.util.continuations._
import scala.util.continuations
import org.scala_lang.virtualized.virtualize
import org.scala_lang.virtualized.SourceContext

import scala.virtualization.lms._
import scala.virtualization.lms.common._
import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable.{Map => MutableMap}
import scala.math._

/*
  this file shows that how high order gradient can be realized via:
  nested forward mode
  forward in reverse (via shift/reset)
  forward in reveser (via cps)
  forward in reverse (via cps) in reverse (via shift/reset)

  the differentiable classes also use tag to handle Perturbation confusion
*/

object highOrder {

  object GlobalTagger {
    var n = 0
    def next() = try n finally n += 1
    def resetTag = {n = 0}
  }

  def compare(a: Int, b: Int): Int = if (a < b) -1 else if (a == b) 0 else +1
  def failwith(s: String): Nothing = throw new Exception(s)

  abstract class Num {
    def +(that: Num): Num
    def *(that: Num): Num
  }

  case class NumV(x: Double) extends Num {
    def + (that: Num) = that match {
      case NumV(bp)         => NumV(x + bp)
      case NumF(bp, bt, bi) => NumF(this + bp, bt, bi)
    }
    def * (that: Num) = that match {
      case NumV(bp)         => NumV(x * bp)
      case NumF(bp, bt, bi) => NumF(this * bp, this * bt, bi)
    }
  }

  case class NumF(x: Num, d: Num, tag: Int) extends Num {
    def + (that: Num) = that match {
      case NumV(bp)         => NumF(x + that, d, tag)
      case NumF(bp, bt, bi) => compare(tag, bi) match {
        case 0  => NumF(x + bp,    d + bt, tag) // tag = bi
        case -1 => NumF(this + bp, bt,     bi)  // tag < bi
        case _  => NumF(x + that,  d,      tag) // tag > bi
      }
    }
    def * (that: Num) = that match {
      case NumV(bp)         => NumF(x * that, d * that, tag)
      case NumF(bp, bt, bi) => compare(tag, bi) match {
        case 0  => NumF(x * bp,    d * bp + x * bt, tag)
        case -1 => NumF(this * bp, this * bt,       bi)
        case _  => NumF(x * that,  d * that,        tag) 
      }
    }
  }

  object Num {
    val Zero = NumV(0.0)
    val One = NumV(1.0)
  }

  implicit class pipeOp[T](x: T) {
    def |>[U](f: T => U): U = f(x)
  }

  def grad(f: Num => Num)(x: Num): Num = NumF(x, Num.One, GlobalTagger.next) |> f |> (x => x.asInstanceOf[NumF].d)

  case class NumR(val x: Num, var d: Num, tag: Int) {
    def + (that: NumR) = shift { k: (NumR => Unit) =>
      val y = new NumR(x + that.x, Num.Zero, max(tag, that.tag))
      k(y)
      compare(tag, that.tag) match {
        case 0  => d = d + y.d; that.d = that.d + y.d
        case -1 => that.d = that.d + y.d
        case _  => d = d + y.d
      }
    }
    def * (that: NumR) = shift { k: (NumR => Unit) =>
      val y = new NumR(x * that.x, Num.Zero, max(tag, that.tag))
      k(y)
      compare(tag, that.tag) match {
        case 0  => d = d + y.d * that.x; that.d = that.d + y.d * x
        case -1 => that.d = that.d + y.d * x
        case _  => d = d + y.d * that.x
      }
    }
  }

  case class Overloaded1()
  implicit val o1: Overloaded1 = Overloaded1()
  def grad(f: NumR => NumR@cps[Unit])(implicit o: Overloaded1) = (x: Num) => {
    val z = new NumR(x, Num.Zero, GlobalTagger.next)
    reset { f(z).d = Num.One }
    z.d
  }

  case class NumR0(val x: Num, var d: Num, tag: Int) {
    def + (that: NumR0) = { k: (NumR0 => Unit) =>
      val y = new NumR0(x + that.x, Num.Zero, max(tag, that.tag))
      k(y)
      compare(tag, that.tag) match {
        case 0  => d = d + y.d; that.d = that.d + y.d
        case -1 => that.d = that.d + y.d
        case _  => d = d + y.d
      }
    }
    def * (that: NumR0) = { k: (NumR0 => Unit) =>
      val y = new NumR0(x * that.x, Num.Zero, max(tag, that.tag))
      k(y)
      compare(tag, that.tag) match {
        case 0  => d = d + y.d * that.x; that.d = that.d + y.d * x
        case -1 => that.d = that.d + y.d * x
        case _  => d = d + y.d * that.x
      }
    }
  }

  case class Overloaded2()
  implicit val o2: Overloaded2 = Overloaded2()
  def grad(f: NumR0 => (NumR0 => Unit) => Unit)(implicit o: Overloaded2) = (x: Num) => {
    val z = new NumR0(x, Num.Zero, GlobalTagger.next)
    f(z)(r => r.d = Num.One)
    z.d
  }

  type Cont = (NumR0 => Unit) => Unit
  class NumRR(val x: NumR0, var d: NumR0, val tag: Int) {
    def + (that: NumRR) = shift { (k: NumRR => Cont) =>
      (p: NumR0 => Unit) => (x + that.x) { t: NumR0 =>
        val y = new NumRR(t, new NumR0(Num.Zero, Num.Zero, 0), max(tag, that.tag))
        k(y) {u: NumR0 => compare(tag, that.tag) match {
          case 0  => (this.d + y.d) {u: NumR0 =>
            this.d = u;
            (that.d + y.d){u: NumR0 =>
              that.d = u
              p(that.d)
            }
          }
          case -1 => (that.d + y.d){u: NumR0 =>
            that.d = u
            p(that.d)
          }
          case _  => (this.d + y.d){u: NumR0 =>
            this.d = u;
            p(this.d)
          }
        }}
      }
    }
    def * (that: NumRR) = shift { (k: NumRR => Cont) =>
      (p: NumR0 => Unit) => (x * that.x) { t: NumR0 =>
        val y = new NumRR(t, new NumR0(Num.Zero, Num.Zero, 0), max(tag, that.tag))
        k(y){u: NumR0 => compare(tag, that.tag) match {
          case 0  => (y.d * that.x){u: NumR0 =>
            (this.d + u){u: NumR0 =>
              this.d = u
              (y.d * this.x){u: NumR0 =>
                (that.d + u){u: NumR0 =>
                  that.d = u
                  p(that.d)
                }
              }
            }
          }
          case -1 => (y.d * this.x){u: NumR0 =>
            (that.d + u){u: NumR0 =>
              that.d = u
              p(that.d)
            }
          }
          case _  => (y.d * that.x){u: NumR0 =>
            (this.d + u){u: NumR0 =>
              this.d = u
              p(this.d)
            }
          }
        }}
      }
    }
    override def toString = (x.toString, d.toString, tag.toString).toString
  }

  case class Overloaded3()
  implicit val o3: Overloaded3 = Overloaded3()
  def grad(f: NumRR => NumRR@cps[Cont])(implicit o: Overloaded3) = (x: NumR0) => {
    val z = new NumRR(x, new NumR0(Num.Zero, Num.Zero, 0), GlobalTagger.next)
    reset {
      f(z).d = new NumR0(Num.One, Num.Zero, 0) // ??? using 0 seems to be correct (not very sure)
      (p: NumR0 => Unit) => p(z.d)
    }
  }


  def assertEqual(a: Num, b: Num): Unit = if (a != b) {
    println(s"$a != $b")
    assert(false)
  }
  def main(args: Array[String]): Unit = {

    println("perturbation confusion in forward mode AD")
    val a = grad { x: Num =>
      val shouldBeOne = grad((y: Num) => x + y)(Num.One)
      println(s"shouldBeOne is $shouldBeOne")
      x * NumF(shouldBeOne, Num.Zero, 0)
    }(Num.One)
    assertEqual(a, NumV(1))
    println(a)

    println("perturbation confusion in reverse mode AD via shift/reset")
    val b = grad { x: NumR =>
      val shouldBeOne = grad((y: NumR) => x + y)(o1)(Num.One)
      println(s"shouldBeOne is $shouldBeOne")
      println(s"x should not yet have any gradient: x = $x")
      x * NumR(shouldBeOne, Num.Zero, 0)
    }(o1)(Num.One)
    assertEqual(b, NumV(1))
    println(b)

    println("perturbation confusion in reverse mode AD via cps")
    val c = grad { x: NumR0 => k =>
      val shouldBeOne = grad((y: NumR0) => k1 => (x + y)(k1))(o2)(Num.One)
      println(s"shouldBeOne is $shouldBeOne")
      println(s"x should not yet have any gradient, but: x = $x")
      (x * NumR0(shouldBeOne, Num.Zero, 0))(k)
    }(o2)(Num.One)
    assertEqual(c, NumV(1))
    println(c)

    println("perturbation confusion in reverse mode AD via cps")
    val d = grad{ grad { x: NumRR =>
      val temp = x
      println(s"x before inner grad should not have any gradient: x = $x")
      val shouldBeTwo = grad(grad((y: NumRR) => (x * y * y))(o3))(o2)(Num.One)
      println(s"shouldBeTwo is $shouldBeTwo")
      println(s"x after inner grad should not have any gradient: x = $x")
      assert(temp == x)
      (x * x * x)
    }(o3)}(o2)(Num.One)
    assertEqual(d, NumV(6))
    println(d)

    println("high order forward mode AD")
    val f = (x: Num) => x * x * x
    val f1: Num => Num = grad(f)
    val f2: Num => Num = grad(f1)
    val f3: Num => Num = grad(f2)

    assertEqual(f1(NumV(4.0)), NumV(48))
    println(f1(NumV(4.0)))

    assertEqual(f2(NumV(4.0)), NumV(24))
    println(f2(NumV(4.0)))

    assertEqual(f3(NumV(4.0)), NumV(6))
    println(f3(NumV(4.0)))

    println("high order reverse mode AD via shift/reset and forward mode AD")
    val g = (x: NumR) => x * x * x
    val g1: Num => Num = grad(g)
    val g2: Num => Num = grad(g1)
    val g3: Num => Num = grad(g2)

    assertEqual(g1(NumV(4.0)), NumV(48))
    println(g1(NumV(4.0)))

    assertEqual(g2(NumV(4.0)), NumV(24))
    println(g2(NumV(4.0)))

    assertEqual(g3(NumV(4.0)), NumV(6))
    println(g3(NumV(4.0)))

    println("high order reverse mode AD via cps and forward mode AD")
    val h = (x: NumR0) => (k: NumR0 => Unit) => (x * x)(r => (r * x)(k))
    val h1: Num => Num = grad(h)
    val h2: Num => Num = grad(h1)
    val h3: Num => Num = grad(h2)

    assertEqual(h1(NumV(4.0)), NumV(48))
    println(h1(NumV(4.0)))

    assertEqual(h2(NumV(4.0)), NumV(24))
    println(h2(NumV(4.0)))

    assertEqual(h3(NumV(4.0)), NumV(6))
    println(h3(NumV(4.0)))

    println("high order reverse mode AD via cps inside reverse mode AD via shift/reset, with forward mode AD")
    def t(x: NumRR) = x * x * x
    val t1: NumR0 => (NumR0 => Unit) => Unit = grad(t)
    val t2: Num => Num = grad(t1)
    val t3: Num => Num = grad(t2)
    
    assertEqual(t2(NumV(4.0)), NumV(24))
    println(t2(NumV(4.0)))

    assertEqual(t3(NumV(4.0)), NumV(6))
    println(t3(NumV(4.0)))
  }
}