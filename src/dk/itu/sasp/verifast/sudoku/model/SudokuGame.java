package dk.itu.sasp.verifast.sudoku.model;

public class SudokuGame {
	private int[][] game;
	
	public SudokuGame() {
		this.game = new int[9][9];
	}

	public static boolean isValidInput(String str) {
		try {
			int i = Integer.parseInt(str);
			if (i > 0 && i <= 9) {
				return true;
			}
		} catch (Exception e) {
			return false;
		}
		return false;
	}
	
	public void setNumber(int x, int y, int number) {
		game[x][y] = number;
		
		System.out.println("Game array changed: ["+x+"]["+y+"] = "+number);
	}
}
