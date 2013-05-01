package dk.itu.sasp.verifast.sudoku.model;

import java.util.Arrays;

public abstract class Utilities {
	// This class is a set of methods that perform common often used methods from the Java Framework.
	// Unfortunately VeriFast doens't allow such method calls, so we abstract from them by adding them to this class
	
	// No instantiation
	private Utilities() { }
	
	public static void sort(int[] array) {
		Arrays.sort(array);
	}
	
	public static int[] copyOfRange(int[] game, int start, int end){
		return Arrays.copyOfRange(game, start, end);
	}
	
	public static double sqrt(int i) {
		return Math.sqrt(i);
	}
}
