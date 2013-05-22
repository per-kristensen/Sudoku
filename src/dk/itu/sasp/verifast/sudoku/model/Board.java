package dk.itu.sasp.verifast.sudoku.model;

/*@

predicate board(Board b, list<int> vs) =	 		b.game |-> ?g &*& g!=null &*& b.N |-> ?n &*& b.x |-> ?x &*& b.y |-> ?y &*& 
                                         			b.number |-> ?number &*& b.size |-> ?size &*& array_slice(g,0,g.length,?elems) &*& 
                                         			0<= size &*& size <= g.length &*& vs == take(size,elems) &*& length(vs) == length(elems);

predicate validBoard(int index, list<int> vs) = 		index < 0 ? true : validMove((index%9),(((index - (index%9))/9) +1), nth(index,vs), vs) &*& validBoard(index-1,vs);

predicate validMove(int x, int y, int number, list<int> vs) = 	validHorizontal(y,number,vs);
	
predicate validHorizontal(int y, int number, list<int> vs) = 	checkRange(y,number) &*& checkUnique(number,take(9,vs));				  		 	

predicate checkUnique(int number, list<int> vs) =  		distinct(remove_every(0,vs)) == true &*& !mem(number,vs);

predicate checkRange(int z, int number) = 			0 <= z &*& z < 9 &*& 0<=number &*& number <= 9;


@*/

public class Board{

  int x,y,number;
  int[]game;
  int N = 9;
  int size = 81;
  
  //Board Constructor
  public Board()
  //@ requires true;
  //@ ensures board(this,?vs);
  {
    game = new int[size];
     //@close board(this,_);
  }
  
  // Checks if a number "number" is allowed at the (x,y) position on the board
  private boolean isValidMove(int x, int y, int number)
  //@ requires board(this,?vs) &*& validMove(x,y,number,vs) &*& length(vs) == 81;
  //@ ensures board(this,vs) &*& result ? validMove(x,y,number,vs) : !result;
  {
        //@ open validMove(x,y,number,vs);
  	return isValidHorizontalMove(y,number);
        //@ close validMove(x,y,number,vs);
  }
  
  // Checks if a number "number" exists on the y row of the board 
  private boolean isValidHorizontalMove(int y, int number)
  //@ requires board(this,?vs) &*& validHorizontal(y,number,vs) &*& length(vs) == 81;
  //@ ensures board(this,vs) &*& validHorizontal(y,number,vs);
  {
  	for(int i = 0; i < 9; i++)
	//@invariant board(this,vs) &*& 0<= i &*& i < length(vs);
	{
	   //@open board(this,vs);
	   if(game[i] == number){
	     //@ close board(this,vs);
	     return false;   
	   }
	 //@ close board(this,vs);  
	}
	return true;
  }
	/*      for-loop to access the correct row on the board, given y.
	
		for (int i = y * N; i < (y + 1) * N; i++)
		//@ invariant board(this,vs) &*& i > 0 &*& i < ((y+1)*N) &*& array_slice(?g,N*y,N*(y+1),_); 
		{...}
	*/
  
 
  // Recursive method using a recursive predicate validBoard
  void validBoard(int size)
  //@ requires board(this,?vs) &*& validBoard(size,vs);
  //@ ensures validBoard(size,vs);
  {
  	if(size > 0){
  	//@ open validBoard(size,vs);
            validBoard(size-1);
        //@ close validBoard(size,vs);
  	}
  }
  
  // Updates the game array with a valid move, uses a given index instead of x and y coords.
  void playMove(int index, int x, int y, int number)
  //@requires board(this, ?vs) &*& validMove(x,y,number,vs) &*& validBoard(length(vs),vs) &*& 0 < index &*& index < length(vs);//assertions about index not needed if program was complete
  //@ensures board(this, ?vs1) &*& validBoard(length(vs),vs); 
  {
    //@ open board(this,vs);
    
    this.x = x;
    this.y = y;
    this.number = number;
    //@ open validMove(x,y,number,vs);
     
     
    //@ open validHorizontal(y,number,vs);
    //@ open checkRange(y,number);
    //@ open checkUnique(number,?hs);
    // assumptions about y and number exposed here
    // index = x+y*9; Cannot assert anything about x+y*9 as there are no assumptions about x
       
       game[index] = number;
 
    //@ close checkUnique(number,hs);
    //@ close checkRange(y,number);
    //@ close validHorizontal(y,number,vs);
    //@ close validMove(x,y,number,vs);
    //@ close board(this,_);
   
  }
}