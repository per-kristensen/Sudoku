package dk.itu.sasp.verifast.sudoku.model;

import java.util.Arrays;

public class SudokuGame2 {

        //@ predicate isValidHorizontalMove(int y) = N |-> ?n &*& game |-> ?g &*& mainY |-> y &*& array_slice(g,n*y,n*(y+1),_);
     
	//@ predicate isValidMove(int x, int y, int number) = mainX |-> x &*& mainY |-> y &*& mainNumber |-> number &*& isValidHorizontalMove(y);
	    // TODO - add isValidVerticalMove + isValidBlockMove predicates to isValidMove predicate
	//@predicate verticalElements(int x) = game |-> ?g &*& N |-> ?n &*& mainX |-> x &*& g[x] |-> _ &*& g[x+n] |-> _ &*& g[x+n+n] |-> _ ;     
	//@predicate fields() = N |-> ?n &*& game |-> ?g &*& n*n>0 &*& mainNumber |-> ?mn &*& mainX |-> ?mx &*& mainY |-> ?my;
	//@predicate array_access(int[] g, int n) = game |-> g &*& N |-> n &*& array_slice(g,0,n*n,_);
	
	
	private final int N = 9;
	private int[] game;
	private int mainY;
	private int mainX;
	private int mainNumber;
	
	public SudokuGame2()
	// possible precondition - N <= sqrt(int.Max)
	//@ requires true;
	//@ ensures fields();
	{ 
	  game = new int[N * N];
	  //@ close fields();
	}

	/*//Methods for determining if a move is valid	
	private boolean isValidMove(int x, int y, int number)
	//@ requires isValidMove(x,y,number); //true
	//@ ensures isValidMove(x,y,number);
	{
		return isValidHorizontalMove(y, number);
				&& isValidVerticalMove(x, number)
				&& isValidBlockMove(x, y, number);
				
	}*/

	private void playMove(int[]game, int x, int y, int number)
	//@requires true; //Board + Move
	//@ensures true; //validMove ? validBoard : !validBoard
	{
	  //game[index] = number;
	}
	
	//Valid horizontal move
	private boolean isValidHorizontalMove(int y, int number)
	//@ requires N |-> ?n &*& game |-> ?g &*& mainY |-> y &*& array_slice(g,n*y,n*(y+1),_) &*& 0<y &*& y<10;
	//@ ensures result ? isValidHorizontalMove(y) : !result;
	{
		for (int i = y * N; i < (y + 1) * N; i++)
		//@ invariant N |-> n &*& game |-> g &*& mainY |-> y &*& i >= n*y &*& array_slice(g,n*y,n*(y+1),_);
		{
			if (game[i] == number) {
				return false;
			}
		}
		return true;
	}
	
	//Valid vertical move
	private boolean isValidVerticalMove(int x, int number)
	//@requires verticalElements(x) &*& N |-> ?n &*& game |-> ?g &*& g!=null;
	//@ensures verticalElements(x);
	{
	        //@open verticalElements(x);
		for (int i = x; i < game.length; i += N)
		//@ invariant game |-> g &*& N|-> n &*& g[i] |-> _;
		  {
			if (game[i] == number) {
				return false;
			}
		}
		//close verticalElements(x);
		return true;
	}

	//Valid block move
	private boolean isValidBlockMove(int x, int y, int number)
	//@ requires game |-> ?g &*& array_slice(g,0,81,_);
	//@ ensures true;
	{
		int blockStartIndex = getBlockStartIndex(getIndex(x, y));
		int[] blockIndicies = getBlockIndicies(blockStartIndex);
		for (int i = 0; i < blockIndicies.length; i++)
		//@ invariant blockIndicies!=null &*& game |-> g &*& i>=0 &*& array_slice(g,0,81,_) &*& array_slice(blockIndicies, 0, blockIndicies.length,_);
		  {
			if (number == game[blockIndicies[i]]) {
				return false;
			}
		}
		return true;
	}

	//Returns the index in one-dimensional array corresponding to x and y coordinates
	private int getIndex(int x, int y)
	//@ requires true;
	//@ ensures true;
	{
		return x + y * N;
	}

	private int getBlockStartIndex(int index) 
	//@ requires true;
	//@ ensures true;
	{
		// 1. get the correct column
		index = index - (index % N);
		// 2. get the correct row
		index = index - (index % N * N * N);
		return index;
	}

	private int[] getBlockIndicies(int blockStartIndex)
	//@ requires true;
	//@ ensures result!=null &*& array_slice(result, 0, result.length, _);
	{
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
	private boolean isValidBoard(int[] game) 
	//@ requires false;
	//@ ensures true;
	{
		return isValidHorizontalBoard(game) && isValidVerticalBoard(game)
				&& isValidBlockBoard(game);
	}

	private boolean isValidHorizontalBoard(int[] game)
	//@ requires false;
	//@ ensures true;
	  {
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

	private boolean isValidVerticalBoard(int[] game) 
	//@ requires false;
	//@ ensures true;
	{
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

	private boolean isValidBlockBoard(int[] game) 
	//@ requires false;
	//@ ensures true;
	{
		int row = 0;
		int groupIndex = 0;
		int sqrtN = (int) Math.sqrt(N);
		while (groupIndex < N * N) {
			row = groupIndex * sqrtN * N;
			for (int first = row; (first + 1) % 9 != 0; first += sqrtN) {
				//get block indicies starting from "first"
				//check if the array is valid
			}
			groupIndex++;
		}
		return false;
	}

	//Returns true if the array has unique numbers in the range 1-9
	//Zeroes are ignored
	private boolean uniqueNumbers(int[] array)
	//@ requires false;
	//@ ensures true;
	  {
		Arrays.sort(array);
		for (int i = 0; i < array.length; i++) {
			if (array[i % array.length] != 0
					&& array[(i + 1) % array.length] != 0
					&& array[i % array.length] == array[(i + 1) % array.length]) {
				return false;
			}
		}
		return true;
	}
}
