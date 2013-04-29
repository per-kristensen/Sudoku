package dk.itu.sasp.verifast.sudoku.model;

//@ predicate validMove(SudokuGame2 sg, int x, int y, int number) = x>0 &*& y>0 &*& number >0;
//@ predicate validNumber(int number) = number > 0 &*& number < 10; 

public class SudokuGame2 {
  
  private int N;
  private int[] game;
  
//@ predicate validSize() = N |-> ?n &*& game |-> ?g &*& g!=null;	
  
  public SudokuGame2(int N)
  //@ requires N*N > 0;
  //@ ensures this.N |-> ?n &*& this.game |-> ?g;
  {
        
  	this.N = N;
     	game = new int[N * N];
     	
  }
  
  public boolean isValidBoard()
  //@ requires false;
  //@ ensures true;
  {
    for(int i = 0; i < game.length; i++){
      if(game[i] == 0) return true;
      else return false;
    }
  }
  
  
  void setNumber(int x, int y, int number)
  //@ requires validSize() &*& validNumber(number) &*& array_slice(g,0,n*n,?elems);
  //@ ensures validSize() &*& validNumber(number) &*& array_slice(g,0,n*n,elems);
  {
     int i = getIndex(x,y);
 
     if(i>0 && i<game.length){
     
        game[i] = number;
     }
  }
  
  int getIndex(int x, int y)
  //@requires N |-> ?n; //&*& array_slice(g,0,n*n,?elems);
  //@ensures N |-> n; // &*& array_slice(g,0,n*n,elems);
  {
  
    return x + y * N;
  
  }
  

	private boolean isValidMove(int x, int y, int number)
	//@ requires validSize() &*& validMove(this,_,_,number); //&*& x > -1 &*& x < n &*& y > -1 &*& y < n;
	//@ ensures validSize() &*& validMove(this,_,_,number);
	{
		return isValidHorizontal(y, number) && isValidVertical(x, number)
				&& isValidBlock(x, y, number);
	}

	private boolean isValidHorizontal(int y, int number)
	//@ requires validSize() &*& validMove(this,_,_,number);//y > -1 &*& y < n &*& this.game |-> ?g;
	//@ ensures validSize() &*& validMove(this,_,y,number);
	{
		for (int i = y * N; i < (y + 1) * N; i++)
		//@ invariant N|-> n &*& i>= y*n &*& y > -1 &*& y < n &*& this.game |-> g;
		{
			if (game[i] == number) {
				return false;
			}
		}
		return true;
	}

	private boolean isValidVertical(int x, int number)
	//@ requires false;
	//@ ensures true;
	{
		for (int i = x; i < game.length; i += N)
		//@ invariant N|-> ?n &*& i>= x*n &*& y > -1 &*& y < n &*& this.game |-> g;
		  {
			if (game[i] == number) {
				return false;
			}
		}
		return true;
	}

	private boolean isValidBlock(int x, int y, int number)
	//@ requires true;
	//@ ensures true;
	{
		// 1. determine the block based on x and y
		// 2. make sure the block has unique values from 1 to 9
		return false;
	}
	*/
}

public class Program{

public Program()
//@ requires true;
//@ ensures true;
{}

  public static void main(String[] args)
  //@ requires true;
  //@ ensures true;
  {

     SudokuGame2 s = new SudokuGame2(9);
  }

}
