package daikon.inv.unary.scalar;

import daikon.*;
import daikon.inv.*;
import daikon.inv.binary.sequenceScalar.*;
import daikon.inv.unary.sequence.*;

import daikon.derive.unary.*;
import daikon.inv.unary.*;
import daikon.suppress.*;

import java.util.*;
import java.util.logging.Level;
import java.util.logging.Logger;
import org.checkerframework.checker.interning.qual.Interned;
import org.checkerframework.checker.lock.qual.GuardSatisfied;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.checker.nullness.qual.NonNull;
import org.checkerframework.dataflow.qual.Pure;
import org.checkerframework.dataflow.qual.SideEffectFree;
import org.checkerframework.framework.qual.Unused;
import org.plumelib.util.Intern;
import typequals.prototype.qual.NonPrototype;
import typequals.prototype.qual.Prototype;

/**
 * Represents the invariant {@code x < c}, where {@code c} is a pre-defined
 * constant representing various integer upper limits, and {@code x} is a 
 * long scalar.
 */
public class IntLimitUpperBound extends SingleScalar {
    static final long serialVersionUID = 20211213L;

    public static boolean dkconfig_enabled = Invariant.invariantEnabledDefault;
    public static final Logger debug = Logger.getLogger("daikon.inv.unary.scalar.IntLimitUpperBound");

    // candidate values for `c`
    public static long[] power_of_two = { 256, 32768, 65536, 1048576, 2147483648L, 4294967296L };
    public static long first_candidate = power_of_two[0];
    public static long last_candidate = power_of_two[power_of_two.length - 1];
    
    public long c = first_candidate;

    IntLimitUpperBound(PptSlice ppt) {
        super(ppt);
    }

    @Prototype IntLimitUpperBound() {
        super();
    }

    private static @Prototype IntLimitUpperBound proto = new @Prototype IntLimitUpperBound();

    /** Returns the prototype invariant for IntLimitUpperBound */
    public static @Prototype IntLimitUpperBound get_proto() {
        return proto;
    }

    /** Returns whether or not this invariant is enabled. */
    @Override
    public boolean enabled() {
        return dkconfig_enabled;
    }

    /** IntLimitUpperBound is only valid on integral types. */
    @Override
    public boolean instantiate_ok(VarInfo[] vis) {

        if (!valid_types(vis)) {
            return false;
        }

        return vis[0].file_rep_type.baseIsIntegral();
    }

    /** instantiate an invariant on the specified slice */
    @Override
    public IntLimitUpperBound instantiate_dyn(@Prototype IntLimitUpperBound this, PptSlice slice) {
        return new IntLimitUpperBound(slice);
    }

    @SideEffectFree
    @Override
    public IntLimitUpperBound clone(@GuardSatisfied IntLimitUpperBound this) {
        IntLimitUpperBound result = (IntLimitUpperBound) super.clone();
        return result;
    }

    @Override
    public String repr(@GuardSatisfied IntLimitUpperBound this) {
        return "IntLimitUpperBound" + varNames();
    }
  
    @SideEffectFree
    @Override
    public String format_using(@GuardSatisfied IntLimitUpperBound this, OutputFormat format) {
      String name = var().name_using(format);
      PptTopLevel pptt = ppt.parent;

      return name + " < " + c;
    }

    @Override
    public InvariantStatus check_modified(long value, int count) {
      return clone().add_modified(value, count);
    }
  
    @Override 
    public InvariantStatus add_modified(long value, int count) {
      if (logDetail() || debug.isLoggable(Level.FINE)) {
        log(
            debug,
            "add_modified (" + value + ",  ppt.num_values = " + ppt.num_values() + ")");
      }
      long largest_candidate = power_of_two[power_of_two.length - 1];

      if (value >= largest_candidate) {
        if (logOn() || debug.isLoggable(Level.FINE))
            log(debug, "destroy in add_modified (" + value + ",  " + count + ")");
        return InvariantStatus.FALSIFIED;
      }
      // value is within the grand bound; now see if need to make c larger
      if (value >= c) {
          // get the next candidate which is larger than c
          for ( long candidate : power_of_two) {
              if (candidate <= c) continue;
              // now new candidate is greater than current bound, 
              // but need to check against current value as well
              if (value >= candidate) continue;
              c = candidate;
              break;
          }
      }
      return InvariantStatus.NO_CHANGE;
    }

    // Used in InvariantChecker.
    // Only check against the current value of c, without modifying it.
    public InvariantStatus add_to_check(long value, int count) {
        if (value >= c) {
            return InvariantStatus.FALSIFIED;
        } else {
            return InvariantStatus.NO_CHANGE;
        }
    }

    @Override
    protected double computeConfidence() {
        return 1 - Math.pow(.5, ppt.num_samples());
    }

    @Pure
    @Override
    public boolean isSameFormula(Invariant other) {
        SingleScalar inv = (SingleScalar) other;
        return this.getClass() == inv.getClass();
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

    /** NI suppressions, initialized in get_ni_suppressions() */
    private static @Nullable NISuppressionSet suppressions = null;

    /** Returns the non-instantiating suppressions for this invariant. */
    @Pure
    @Override
    public @NonNull NISuppressionSet get_ni_suppressions() {
        if (suppressions == null) {

        NISuppressee suppressee = new NISuppressee(IntLimitUpperBound.class, 1);

        // suppressor definitions (used in suppressions below)

        // NISuppressor v_upper = new NISuppressor(0, UpperBound.class);
        NISuppressor near_zero = new NISuppressor(0, PositiveNearZero.class);

        suppressions =
            new NISuppressionSet(
                new NISuppression[] {

                    // // v <= a => v < c, if a << c
                    // new NISuppression(v_upper, suppressee),
                    // 0 <= v <= a => v < c, if a << c
                    new NISuppression(near_zero, suppressee),

                });
        }
        return suppressions;
    }
        
}
