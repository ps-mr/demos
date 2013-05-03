/*
 * Kiama demo by Jonathan Brachthäuser
 * 
 * This demo is a follow up to [1], partly inspired by [2]
 * 
 * [1] : https://github.com/yfcai/demos/blob/master/plt-redex.rkt
 * [2] : https://code.google.com/p/kiama/source/browse/kiama/src/org/kiama/example/lambda/Lambda.scala
 */
import org.kiama.attribution.Attributable
import org.kiama.util.{ Positioned, PositionedParserUtilities }
import org.kiama.rewriting.Rewriter._
import org.kiama.util.ParsingREPL
import org.kiama.output.{ ParenPrettyPrinter, PrettyPrinter }
import org.kiama.attribution.Attribution.{ attr, paramAttr, CachedParamAttribute }

/*
 * Abstract syntax tree is represented as usual by case classes
 */
abstract class Exp extends Attributable with Positioned
case class Num(n: Int) extends Exp
case class Add(lhs: Exp, rhs: Exp) extends Exp
case class Mul(lhs: Exp, rhs: Exp) extends Exp
case class Id(s: Symbol) extends Exp


/*
 * Kiama provides some cool parsing utilities like automatic uncurrying of functions
 */
trait AEParser extends PositionedParserUtilities {

  // Lexer
  lazy val name: PackratParser[Symbol] = "[a-zA-Z][a-zA-Z0-9]*".r ^^ {
    case name => Symbol(name)
  }
  
  lazy val int = "[0-9]+".r ^^ {
    case value => value.toInt
  }
  
  // Parser
  lazy val exp = add
  
  lazy val add: PackratParser[Exp] = 
    ((add <~ "+") ~ mul ^^ Add
    | mul
    )
  lazy val mul: PackratParser[Exp] = 
    ((mul <~ "*") ~ lit ^^ Mul
    | unary
    )
  
  // This is needed later on to extend the AE language
  lazy val unary = lit
    
  lazy val lit: PackratParser[Exp] =
    name ^^ Id | int ^^ Num | "(" ~> exp <~ ")"
  
}

/*
 * Kiama also offers pretty printing facilities based on document combinators
 */
trait AEPrettyPrinter extends ParenPrettyPrinter with PrettyPrinter {
  def toDoc(e: Exp): Doc = e match {
    case Num(n) => value(n)
    case Id(s) => s.name
    case Add(lhs, rhs) => parens (toDoc(lhs) <+> "+" <+> toDoc(rhs))
    case Mul(lhs, rhs) => parens (toDoc(lhs) <+> "*" <+> toDoc(rhs))
  }
}

/*
 * The semantics are implemented using stratego like AST rewriting
 */
trait AESemantics {
  
  val addition = rule {
    case Add(Num(x), Num(y)) => Num(x+y)
  }
  
  val multiplication = rule {
    case Mul(Num(x), Num(y)) => Num(x*y)
  }
  
  val arithmetics = addition + multiplication
  
  val arithReduction = bottomup(attempt(arithmetics))
  
  def eval(e: Exp): Exp = rewrite(arithReduction)(e)
  
}

/*
 * We can can now mix all our features together and get a REPL for free!
 */
trait REPL extends ParsingREPL[Exp] { self: AEParser with AESemantics =>
  // prettyprinter is an object, since it often causes name clashes when mixed in
  val pp: AEPrettyPrinter
  
  // start rule of the parser
  def start: Parser[Exp] = exp
  
  def process(tree: Exp) {
    emitter.emitln( pp.pretty( pp.toDoc( eval(tree) ) ) )
  }
}

object AERepl extends REPL with AEParser with AESemantics {  
  object pp extends AEPrettyPrinter
}

/*
 * Now it's time to extend the language with functions
 */
case class Fun(param: Symbol, body: Exp) extends Exp
case class App(fun: Exp, arg: Exp) extends Exp
  
// syntactic sugar
case class Fun_*(args: List[Symbol], body: Exp) extends Exp


/*
 * The parser extension is pretty straight forward
 */
trait FAEParser extends AEParser {

  override lazy val exp: PackratParser[Exp] =
    (("\\" ~> name <~ ".") ~ exp ^^ Fun
    | add
    )
    
  lazy val app: PackratParser[Exp] =
    ( app ~ lit ^^ App
    | lit
    )
    
  override lazy val unary = app
}

/*
 * Extending the prettyprinter also is nothing special here
 */
trait FAEPrettyPrinter extends AEPrettyPrinter {
  override def toDoc(e: Exp): Doc = e match {
    case Fun(param, body) => backslash <> param.name <> dot <> nest ( line <> toDoc(body))
    case App(lhs, rhs) => toDoc(lhs) <+> toDoc(rhs)
    case other => super.toDoc(other)
  }
}

/*
 * For implementation the reductions we follow the \xgc-reduction implementation as seen in [2]
 */
trait FAESemantics extends AESemantics {

  case class Sub(x: Symbol, by: Exp, in: Exp) extends Exp
  
  val fv: Exp => Set[Symbol] = attr {
    case Id(i) 			       => Set(i)
    case Fun(x, body)      => body->fv - x
    case Sub(x, by, in)    => (in->fv - x) ++ (by->fv)
    case Term(p, children) => children.collect {
      case e: Exp => e->fv
    }.foldLeft[Set[Symbol]](Set.empty)(_ ++ _)
  }

  val reduction = rule {
    case App(Fun(x, body), arg) => Sub(x, arg, body)
    
    // Garbage collection
    case Sub(x, by, in) if !(in->fv contains x) => in

    case Sub(x, by, Id(y)) if x == y => by
    
    case Sub(x, by, in) => rewrite ( all ( rule {
      case e: Exp => Sub(x, by, e)
      case other => other
    })) (in)
  }
  
  val desugering = rule {
    case Fun_*(args, body) => args.foldRight(body)(Fun)
  }
  
  override def eval(e: Exp) = rewrite ( 
      reduce(desugering) <* outermost(reduction) <* arithReduction
 )(e)
  
}

object FAERepl extends REPL with FAEParser with FAESemantics {
  object pp extends FAEPrettyPrinter  
}