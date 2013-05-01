package dk.itu.sasp.verifast.sudoku.model;

import java.util.Arrays;

public class SudokuGame2 {

	private final int N = 9;
	private int[] game;

	public SudokuGame2()
	// possible precondition - N <= sqrt(int.Max)
	//@ requires N |-> ?n &*& n*n >0 &*& n>0;
	//@ ensures true;
	{
		game = new int[N * N];
	}

	//Methods for determining if a move is valid	
	private boolean isValidMove(int x, int y, int number)
	//@ requires N |-> ?n &*& x > -1 &*& x < n &*& y > -1 &*& y < n;
	//@ ensures true;
	{
		return isValidHorizontalMove(y, number)
				&& isValidVerticalMove(x, number)
				&& isValidBlockMove(x, y, number);
	}

	//Valid horizontal move
	private boolean isValidHorizontalMove(int y, int number)
	/*
	 * @ requires N |-> ?n &*& game |-> ?g &*& 0 < number &*& number <= n &*& 0
	 * < y &*& y < n &*& array_slice(g,0,n*n,_) &*& array_element(g,_,_);
	 * 
	 * @
	 */
	//@ ensures true;
	{
		for (int i = y * N; i < (y + 1) * N; i++)
		//@ invariant N |-> n &*& game |-> g &*& array_element(g,i,_);//array_slice(g,0,n*n,_) &*& g[i] |-> _;
		{
			if (game[i] == number) {
				return false;
			}
		}
		return true;
	}

	//Valid vertical move
	private boolean isValidVerticalMove(int x, int number)
	//@requires false;
	//@ensures true;
	{
		for (int i = x; i < game.length; i += N) {
			if (game[i] == number) {
				return false;
			}
		}
		return true;
	}

	//Valid block move
	private boolean isValidBlockMove(int x, int y, int number)
	//@ requires true;
	//@ ensures true;
	{
		int index = getIndex(x, y);
		int blockStartIndex = getBlockStartIndex(index);
		int[] blockIndicies = getBlockIndicies(blockStartIndex);
		for (int i = 0; i < blockIndicies.length; i++) {
			if (number == game[blockIndicies[i]]) {
				return false;
			}
		}
		return true;
	}

	//Returns the index in one-dimensional array corresponding to x and y coordinates
	private int getIndex(int x, int y) {
		return x + y * N;
	}

	private int getBlockStartIndex(int index) {
		// 1. get the correct column
		index = index - (index % N);
		// 2. get the correct row
		index = index - (index % N * N * N);
		return index;
	}

	private int[] getBlockIndicies(int blockStartIndex) {
		int[] indicies = new int[N];
		int sqrtN = (int) Math.sqrt(N);
		for (int i = 0; i < indicies.length; i++) {
			indicies[i] = blockStartIndex;
			for (int j = 0; j < sqrtN; j++) {
				blockStartIndex++;
			}
			blockStartIndex += N;
		}
		return indicies;
	}

	//Methods for determining if a board is valid
	private boolean isValidBoard(int[] game) {
		return isValidHorizontalBoard(game) && isValidVerticalBoard(game)
				&& isValidBlockBoard(game);
	}

	private boolean isValidHorizontalBoard(int[] game) {
		int start = 0;
		int end = 0;
		while (end < N * N) {
			end = start + N;
			int[] row = Arrays.copyOfRange(game, start, end);
			if (!uniqueNumbers(row)) {
				return false;
			}
			start += N;
		}
		return true;
	}

	private boolean isValidVerticalBoard(int[] game) {
		int[] column;
		int x = 0;
		int y = 0;
		while (x < N) {
			y = x;
			column = new int[N];
			for (int i = 0; i < N; i++) {
				column[i] = game[y];
				y += N;
			}
			if (!uniqueNumbers(column)) {
				return false;
			}
			x++;
		}
		return true;
	}

	private boolean isValidBlockBoard(int[] game) {
		int firstStartIndex = 0;
		int currentStartIndex = 0;
		int sqrtN = (int) Math.sqrt(N);
		while (currentStartIndex < N * N) {
			//traverse all the blocks on the row
			currentStartIndex = firstStartIndex;
			do {
				int[] blockIndicies = getBlockIndicies(currentStartIndex);
				int[] blockValues = new int[blockIndicies.length];
				for (int i = 0; i < blockIndicies.length; i++) {
					blockValues[i] = game[blockIndicies[i]];
				}
				currentStartIndex += sqrtN;//move to the next block start index
			} while (currentStartIndex % N != 0);

			//move the start index to the next blocks row
			firstStartIndex += N * sqrtN;
		}
		return false;
	}

	//Returns true if the array has unique numbers in the range 1-9
	//Zeroes are ignored
	private boolean uniqueNumbers(int[] array) {
		Arrays.sort(array);
		int current, next;
		for (int i = 0; i < array.length; i++) {
			current = array[i % array.length];
			next = array[(i + 1) % array.length];

			if ((current != 0 && next != 0 && current == next) || current < 0
					|| current > N) {
				return false;
			}
		}
		return true;
	}
}
