package daikon.inv.binary.twoScalar;

import daikon.*;
import daikon.derive.binary.*;
import daikon.derive.unary.*;
import daikon.inv.*;
import daikon.inv.binary.twoScalar.*;
import daikon.inv.binary.twoSequence.*;
import daikon.inv.unary.scalar.*;
import daikon.inv.unary.sequence.*;
import daikon.inv.unary.string.*;
import daikon.suppress.*;
import java.util.*;
import java.util.logging.Level;
import java.util.logging.Logger;
import org.checkerframework.checker.interning.qual.Interned;
import org.checkerframework.checker.lock.qual.GuardSatisfied;
import org.checkerframework.checker.nullness.qual.NonNull;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.dataflow.qual.Pure;
import org.checkerframework.dataflow.qual.SideEffectFree;
import org.plumelib.util.Intern;
import typequals.prototype.qual.NonPrototype;
import typequals.prototype.qual.Prototype;

/**
 * Represents an invariant of &ge; between diffenrence of two long scalars, and constant.
 * Prints as {@code x - y >= a}.
 */
public final class IntDiffGreaterThan extends TwoScalar {

  // We are Serializable, so we specify a version to allow changes to
  // method signatures without breaking serialization.  If you add or
  // remove fields, you should change this number to the current date.
  static final long serialVersionUID = 20211129L;

  // Variables starting with dkconfig_ should only be set via the
  // daikon.config.Configuration interface.
  /** Boolean. True iff IntDiffGreaterThan invariants should be considered. */
  public static boolean dkconfig_enabled = Invariant.invariantEnabledDefault;

  public static final Logger debug = Logger.getLogger("daikon.inv.binary.twoScalar.IntDiffGreaterThan");

  // tunable parameters. controls min max values of the (lower bound) constant
  public static final long MAX_A = 100000, MIN_A = 1;
  // upper bound for interesting a - two variables that are very far apart
  // are not interesting
  public static final long interesting_upper_bound = 50;
  // the constant in the invariant x - y >= a
  public long a = MAX_A;

  IntDiffGreaterThan(PptSlice ppt, boolean swap) {
    super(ppt);
    this.swap = swap;
  }

  @Prototype IntDiffGreaterThan(boolean swap) {
    super();
    this.swap = swap;
  }

  private static @Prototype IntDiffGreaterThan proto = new @Prototype IntDiffGreaterThan(false);
  private static @Prototype IntDiffGreaterThan proto_swap = new @Prototype IntDiffGreaterThan(true);

  /** Returns the prototype invariant for IntDiffGreaterThan */
  public static @Prototype IntDiffGreaterThan get_proto(boolean swap) {
    if (swap) {
      return proto_swap;
    } else {
      return proto;
    }
  }

  /** Returns whether or not this invariant is enabled. */
  @Override
  public boolean enabled() {
    return dkconfig_enabled;
  }

  /** Returns whether or not the specified var types are valid for IntGreaterEqual */
  @Override
  public boolean instantiate_ok(VarInfo[] vis) {

    if (!valid_types(vis)) {
      return false;
    }

        return (vis[0].file_rep_type.isIntegral()
                && vis[1].file_rep_type.isIntegral());

  }

  /** Instantiate an invariant on the specified slice. */
  @Override
  protected IntDiffGreaterThan instantiate_dyn(@Prototype IntDiffGreaterThan this, PptSlice slice) {

    return new IntDiffGreaterThan(slice, swap);
  }

  // JHP: this should be removed in favor of checks in PptTopLevel
  // such as is_equal, is_lessequal, etc.
  // Look up a previously instantiated IntGreaterEqual relationship.
  // Should this implementation be made more efficient?

  // TODO: is this used anywhere?
  public static @Nullable IntDiffGreaterThan find(PptSlice ppt) {
    assert ppt.arity() == 2;
    for (Invariant inv : ppt.invs) {
      if (inv instanceof IntDiffGreaterThan) {
        return (IntDiffGreaterThan) inv;
      }
    }
    return null;
  }

  @Override
  public String repr(@GuardSatisfied IntDiffGreaterThan this) {
    return "IntDiffGreaterThan" + varNames();
  }

  @SideEffectFree
  @Override
  public String format_using(@GuardSatisfied IntDiffGreaterThan this, OutputFormat format) {

    String var1name = var1().name_using(format);
    String var2name = var2().name_using(format);

    if ((format == OutputFormat.DAIKON) || (format == OutputFormat.ESCJAVA)) {
        String comparator = ">=";
        return var1name + " - " + var2name + " " + comparator + " " + a;
    }

    if (format == OutputFormat.CSHARPCONTRACT) {
        String comparator = ">=";
        return var1name + " - " + var2name + " " + comparator + " " + a;
    }

    if (format.isJavaFamily()) {

        if ((var1name.indexOf("daikon.Quant.collectObject") != -1)

            || (var2name.indexOf("daikon.Quant.collectObject") != -1)) {
          return "(warning: it is meaningless to compare hashcodes for values obtained through daikon.Quant.collect... methods:"
            + var1name + " - " + var2name + " >= " + a + ")";
        }
        return var1name + " - " + var2name + " >= " + a;
    }

    return format_unimplemented(format);
  }

  @SideEffectFree
  @Override
  public IntDiffGreaterThan clone(@GuardSatisfied IntDiffGreaterThan this) {
    IntDiffGreaterThan result = (IntDiffGreaterThan) super.clone();
    return result;
  }

  @Override
  @SuppressWarnings("UnnecessaryParentheses")  // generated code; parens are sometimes necessary
  public InvariantStatus check_modified(long v1, long v2, int count) {
    return clone().add_modified(v1, v2, count);
  }

  @Override
  public InvariantStatus add_modified(long v1, long v2, int count) {
    if (logDetail() || debug.isLoggable(Level.FINE)) {
      log(
          debug,
          "add_modified (" + v1 + ", " + v2 + ",  ppt.num_values = " + ppt.num_values() + ")");
    }
    long diff = v1 - v2;
    if (diff > MAX_A || diff < MIN_A) {
        if (logOn() || debug.isLoggable(Level.FINE))
            log(debug, "destroy in add_modified (" + v1 + ", " + v2 + ",  " + count + ")");
        return InvariantStatus.FALSIFIED;
    }
    // now diff should be in range [MAX_A, MIN_A]
    // use new samples to push a to lower values
    if (diff < a)
        a = diff; // update bound

    return InvariantStatus.NO_CHANGE;
  }

  // Used in InvariantChecker.
  // Only check against the current value of a, without modifying it.
  public InvariantStatus add_to_check(long v1, long v2, int count) {
    if (a >= interesting_upper_bound) {
      // InvaraintChecker filters out uninteresting invariants with large a
      // if InvariantChecker sees a NO_CHANGE sample, this invariant will not
      // be returned
      return InvariantStatus.NO_CHANGE;
    }
    long diff = v1 - v2;
    if (diff < a) {
        return InvariantStatus.FALSIFIED;
    } else {
        return InvariantStatus.NO_CHANGE;
    }
  }

  // This is very tricky, because whether two variables are equal should
  // presumably be transitive, but it's not guaranteed to be so when using
  // this method and not dropping out all variables whose values are ever
  // missing.
  @Override
  protected double computeConfidence() {
    return 1 - Math.pow(.5, ppt.num_samples());
  }

  @Pure
  @Override
  public boolean isExact() {
      return false;
  }

  // // Temporary, for debugging
  // public void destroy() {
  //   if (debug.isLoggable(Level.FINE)) {
  //     System.out.println("IntGreaterEqual.destroy(" + ppt.name() + ")");
  //     System.out.println(repr());
  //     (new Error()).printStackTrace();
  //   }
  //   super.destroy();
  // }

  @Override
  public InvariantStatus add(
      @Interned Object v1, @Interned Object v2, int mod_index, int count) {
    if (debug.isLoggable(Level.FINE)) {
      debug.fine(
          "IntDiffGreaterThan"
          + ppt.varNames()
          + ".add("
          + v1
          + ","
          + v2
          + ", mod_index="
          + mod_index
          + "), count="
          + count
          + ")");
    }
    return super.add(v1, v2, mod_index, count);
  }

  @Pure
  @Override
  public boolean isExclusiveFormula(Invariant other) {
    return false;
  }

  @Override
  public @Nullable DiscardInfo isObviousStatically(VarInfo[] vis) {
    return super.isObviousStatically(vis);
  }

  @Pure
  @Override
  public @Nullable DiscardInfo isObviousDynamically(VarInfo[] vis) {
    DiscardInfo super_result = super.isObviousDynamically(vis);
    return super_result;
  } // isObviousDynamically


  /** Returns the non-instantiating suppressions for this invariant. */
  @Pure
  @Override
  public @NonNull NISuppressionSet get_ni_suppressions() {
    if (swap) {
      return suppressions_swap;
    } else {
      return suppressions;
    }
  }

  // suppressee (unswapped)
  private static NISuppressee suppressee = new NISuppressee(IntDiffGreaterThan.class, false);

  private static NISuppressor v1_eq_v2 = new NISuppressor(0, 1, IntEqual.class);

  private static NISuppressionSet suppressions =
    new NISuppressionSet(
        new NISuppression[] {

            // v1 == v2 => v1 - v2 >= 0
            new NISuppression(v1_eq_v2, suppressee),

        });
  private static NISuppressionSet suppressions_swap = suppressions.swap();
}
