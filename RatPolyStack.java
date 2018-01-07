package hw4;

import java.util.Iterator;
import java.util.Stack;

/**
 * <b>RatPolyStack</B> is a mutable finite sequence of RatPoly objects.
 * <p>
 * Each RatPolyStack can be described by [p1, p2, ... ], where [] is an empty
 * stack, [p1] is a one element stack containing the Poly 'p1', and so on.
 * RatPolyStacks can also be described constructively, with the append
 * operation, ':'. such that [p1]:S is the result of putting p1 at the front of
 * the RatPolyStack S.
 * <p>
 * A finite sequence has an associated size, corresponding to the number of
 * elements in the sequence. Thus the size of [] is 0, the size of [p1] is 1,
 * the size of [p1, p1] is 2, and so on.
 * <p>
 */
public final class RatPolyStack implements Iterable<RatPoly> {

	private final Stack<RatPoly> polys;

	// Abstraction Function:
	// Each element of a RatPolyStack, s, is mapped to the
	// corresponding element of polys.
	//
	// RepInvariant:
	// polys != null &&
	// forall i such that (0 <= i < polys.size(), polys.get(i) != null

	/**
	 * @effects Constructs a new RatPolyStack, [].
	 */
	public RatPolyStack() {
		polys = new Stack<RatPoly>();
		checkRep();
	}

	/**
	 * Returns the number of RayPolys in this RatPolyStack.
	 *
	 * @return the size of this sequence.
	 */
	public int size() {
		// returning size of polys
		return polys.size();
	}

	/**
	 * Pushes a RatPoly onto the top of this.
	 *
	 * @param p
	 *            The RatPoly to push onto this stack.
	 * @requires p != null
	 * @modifies this
	 * @effects this_post = [p]:this
	 */
	public void push(RatPoly p) {
		checkRep();
		// pushing p into the stack
		polys.push(p);
		checkRep();

	}

	/**
	 * Removes and returns the top RatPoly.
	 *
	 * @requires this.size() > 0
	 * @modifies this
	 * @effects If this = [p]:S then this_post = S
	 * @return p where this = [p]:S
	 */
	public RatPoly pop() {
		checkRep();
		// save a copy of top to return later
		RatPoly top;
		// popping the top off
		top = polys.pop();
		checkRep();
		return top;
	}

	/**
	 * Duplicates the top RatPoly on this.
	 *
	 * @requires this.size() > 0
	 * @modifies this
	 * @effects If this = [p]:S then this_post = [p, p]:S
	 */
	public void dup() {
		checkRep();
		// save the top of the stack
		RatPoly top = polys.peek();
		// push the duplicate of the top in
		polys.push(top);
		checkRep();

	}

	/**
	 * Swaps the top two elements of this.
	 *
	 * @requires this.size() >= 2
	 * @modifies this
	 * @effects If this = [p1, p2]:S then this_post = [p2, p1]:S
	 */
	public void swap() {
		checkRep();
		// save a copy of the top of the stack
		RatPoly p1 = polys.peek();
		// pop it off
		polys.pop();
		// save a copy of the top of the stack again
		RatPoly p2 = polys.peek();
		// pop it off
		polys.pop();
		// push the last one popped
		polys.push(p1);
		// push the first one popped
		polys.push(p2);
		checkRep();
	}

	/**
	 * Clears the stack.
	 *
	 * @modifies this
	 * @effects this_post = []
	 */
	public void clear() {
		checkRep();
		polys.clear();
		checkRep();
	}

	/**
	 * Returns the RatPoly that is 'index' elements from the top of the stack.
	 *
	 * @param index
	 *            The index of the RatPoly to be retrieved.
	 * @requires index >= 0 && index < this.size()
	 * @return If this = S:[p]:T where S.size() = index, then returns p.
	 */
	public RatPoly getNthFromTop(int index) {
		checkRep();
		// create a temp stack
		Stack<RatPoly> temp = new Stack<RatPoly>();
		// push into the temp stack and pop from polys until the nth from top
		// term
		for (int i = 0; i < index; i++)
			temp.push(polys.pop());
		// save a copy of the nth from top term
		RatPoly p = polys.peek();
		// push the items in temp stack back into polys
		for (int i = 0; i < index; i++)
			polys.push(temp.pop());
		checkRep();
		// return the nth from top term
		return p;
	}

	/**
	 * Pops two elements off of the stack, adds them, and places the result on
	 * top of the stack.
	 *
	 * @requires this.size() >= 2
	 * @modifies this
	 * @effects If this = [p1, p2]:S then this_post = [p3]:S where p3 = p1 + p2
	 */
	public void add() {
		checkRep();
		// pop the two RatPolys out
		RatPoly r1 = polys.pop();
		RatPoly r2 = polys.pop();
		// add the two RatPoly together and push it back in
		polys.push(r1.add(r2));
		checkRep();
	}

	/**
	 * Subtracts the top poly from the next from top poly, pops both off the
	 * stack, and places the result on top of the stack.
	 *
	 * @requires this.size() >= 2
	 * @modifies this
	 * @effects If this = [p1, p2]:S then this_post = [p3]:S where p3 = p2 - p1
	 */
	public void sub() {
		checkRep();
		// pop the two RatPolys out
		RatPoly r1 = polys.pop();
		RatPoly r2 = polys.pop();
		// sub one RatPoly from the other and push it back in
		polys.push(r2.sub(r1));
		checkRep();
	}

	/**
	 * Pops two elements off of the stack, multiplies them, and places the
	 * result on top of the stack.
	 *
	 * @requires this.size() >= 2
	 * @modifies this
	 * @effects If this = [p1, p2]:S then this_post = [p3]:S where p3 = p1 * p2
	 */
	public void mul() {
		checkRep();
		// pop the two RatPolys out
		RatPoly r1 = polys.pop();
		RatPoly r2 = polys.pop();
		// multiply the two RatPolys and push it back in
		polys.push(r1.mul(r2));
		checkRep();
	}

	/**
	 * Divides the next from top poly by the top poly, pops both off the stack,
	 * and places the result on top of the stack.
	 *
	 * @requires this.size() >= 2
	 * @modifies this
	 * @effects If this = [p1, p2]:S then this_post = [p3]:S where p3 = p2 / p1
	 */
	public void div() {
		checkRep();
		// pop the two RatPolys out
		RatPoly r1 = polys.pop();
		RatPoly r2 = polys.pop();
		// divide one RatPoly from the other and push it back in
		polys.push(r2.div(r1));
		checkRep();

	}

	/**
	 * Pops the top element off of the stack, differentiates it, and places the
	 * result on top of the stack.
	 *
	 * @requires this.size() >= 1
	 * @modifies this
	 * @effects If this = [p1]:S then this_post = [p2]:S where p2 = derivative
	 *          of p1
	 */
	public void differentiate() {
		checkRep();
		// pop the element
		RatPoly r = polys.pop();
		// differentiate the element
		polys.push(r.differentiate());
		checkRep();
	}

	/**
	 * Pops the top element off of the stack, integrates it, and places the
	 * result on top of the stack.
	 *
	 * @requires this.size() >= 1
	 * @modifies this
	 * @effects If this = [p1]:S then this_post = [p2]:S where p2 = indefinite
	 *          integral of p1 with integration constant 0
	 */
	public void integrate() {
		checkRep();
		// pop the element
		RatPoly r = polys.pop();
		// integrate the element
		polys.push(r.antiDifferentiate(new RatNum(0)));
		checkRep();
	}

	/**
	 * Returns an iterator of the elements contained in the stack.
	 *
	 * @return an iterator of the elements contained in the stack in order from
	 *         the bottom of the stack to the top of the stack.
	 */
	@Override
	public Iterator<RatPoly> iterator() {
		return polys.iterator();
	}

	/**
	 * Checks that the representation invariant holds (if any).
	 */
	private void checkRep() {
		assert (polys != null) : "polys should never be null.";

		for (RatPoly p : polys) {
			assert (p != null) : "polys should never contain a null element.";
		}
	}
}
