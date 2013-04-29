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
	//@ requires N |-> ?n &*& y > -1 &*& y < n;
	//@ ensures true;
	{
		//get the beginning of the row
		int x = getIndex(0, y);
		while ((x + 1) % N != 0)
		//@ invariant true;
		{
			if (game[x] == number) {
				return false;
			}
			x++;
		}
		return true;
	}

	//Valid vertical move
	private boolean isValidVerticalMove(int x, int number)
	//@ requires N |-> ?n &*& x > -1 &*& x < n;
	//@ ensures x > -1 &*& x < n;
	{
		//get the beginning of the column
		int y = getIndex(x, 0);
		while (y < N * N) {
			if (game[y] == number) {
				return false;
			}
			y += N;
		}
		return true;
	}

	//Valid block move
	private boolean isValidBlockMove(int x, int y, int number)
	//@ requires true;
	//@ ensures true;
	{
		int blockStartIndex = getBlockStartIndex(getIndex(x, y));
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
		for (int i = 0; i < indicies.length; i++) {
			indicies[i] = blockStartIndex;
			for (int j = 0; j < Math.sqrt(N); j++) {
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
		// TODO Auto-generated method stub

		//while start index < N * N
		//increase startIndex by ?
		//get the block indices
		//for each block
		//check if the array consists of unique numbers
		return false;
	}

	//Returns true if the array has unique numbers in the range 1-9
	//Zeroes are ignored
	private boolean uniqueNumbers(int[] array) {
		Arrays.sort(array);
		for (int i = 0; i < N; i++) {
			if (array[i % N] != 0 && array[(i + 1) % N] != 0
					&& array[i % N] == array[(i + 1) % N]) {
				return false;
			}
		}
		return true;
	}
}
