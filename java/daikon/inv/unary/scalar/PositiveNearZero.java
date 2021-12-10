package daikon.inv.unary.scalar;

import daikon.*;
import daikon.inv.*;
import daikon.inv.binary.sequenceScalar.*;
import daikon.inv.unary.sequence.*;

import daikon.derive.unary.*;
import daikon.inv.unary.*;
import java.util.*;
import java.util.logging.Level;
import java.util.logging.Logger;
import org.checkerframework.checker.interning.qual.Interned;
import org.checkerframework.checker.lock.qual.GuardSatisfied;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.dataflow.qual.Pure;
import org.checkerframework.dataflow.qual.SideEffectFree;
import org.checkerframework.framework.qual.Unused;
import org.plumelib.util.Intern;
import typequals.prototype.qual.NonPrototype;
import typequals.prototype.qual.Prototype;

/**
 * Represents the invariant {@code 0<= x <= c}, where {@code c} is a constant and
 * {@code x} is a long scalar.
 */
public class PositiveNearZero extends SingleScalar {
    static final long serialVersionUID = 20211209L;

    public static boolean dkconfig_enabled = Invariant.invariantEnabledDefault;
    public static final Logger debug = Logger.getLogger("daikon.inv.unary.scalar.PositiveNearZero");

    public static long MAX_C = 10;
    
    public long c = MAX_C;

    PositiveNearZero(PptSlice ppt) {
        super(ppt);
      }

    @Prototype PositiveNearZero() {
        super();
    }

    private static @Prototype PositiveNearZero proto = new @Prototype PositiveNearZero();

    /** Returns the prototype invariant for IntDiffGreaterThan */
    public static @Prototype PositiveNearZero get_proto() {
        return proto;
    }

    /** Returns whether or not this invariant is enabled. */
    @Override
    public boolean enabled() {
        return dkconfig_enabled;
    }

    /** PositiveNearZero is only valid on integral types. */
    @Override
    public boolean instantiate_ok(VarInfo[] vis) {

        if (!valid_types(vis)) {
        return false;
        }

        return vis[0].file_rep_type.baseIsIntegral();
    }

    /** instantiate an invariant on the specified slice */
    @Override
    public PositiveNearZero instantiate_dyn(@Prototype PositiveNearZero this, PptSlice slice) {
        return new PositiveNearZero(slice);
    }

    @SideEffectFree
    @Override
    public PositiveNearZero clone(@GuardSatisfied PositiveNearZero this) {
        PositiveNearZero result = (PositiveNearZero) super.clone();
        return result;
    }

    @Override
    public String repr(@GuardSatisfied PositiveNearZero this) {
        return "PositiveNearZero" + varNames();
    }
  
    @SideEffectFree
    @Override
    public String format_using(@GuardSatisfied PositiveNearZero this, OutputFormat format) {
      String name = var().name_using(format);
      PptTopLevel pptt = ppt.parent;

      return name + " <= " + c;
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
      if (value < 0 || value > c) {
        if (logOn() || debug.isLoggable(Level.FINE))
            log(debug, "destroy in add_modified (" + value + ",  " + count + ")");
        return InvariantStatus.FALSIFIED;
      }
      if (value < c)
          c = value;
      
      return InvariantStatus.NO_CHANGE;
    }

    // Used in InvariantChecker.
    // Only check against the current value of c, without modifying it.
    public InvariantStatus add_to_check(long value, int count) {
        if (value < 0 || value > c) {
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
        
}
