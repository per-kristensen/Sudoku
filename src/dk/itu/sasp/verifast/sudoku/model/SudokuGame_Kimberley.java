package dk.itu.sasp.verifast.sudoku.model;

public class SudokuGame_Kimberley {

  private int N;
	private int game[];

	SudokuGame_Kimberley(int N, int[] game) {

		this.N = N;
		this.game = game;
	}

	public boolean isValidBoard() {

		// All vertical elements are valid

		int start = 0;
		int end = 0;

		while (end < N * N) {

			end += N;
			int[] tmp = new int[N];

			for (int i = 0; i < N; i++) {
				tmp[i] = game[start];
				start += N;
				System.out.println(tmp[i]);
			}

			for (int i = 0; i < N; i++) {
				if (tmp[i % N] != 0 && tmp[i % N] == tmp[(i + 1) % N]
						&& tmp[(i + 1) % N] != 0) {
					return false;
				}
			}
		}
		return true;
		/*
		 * // All horizontal elements are valid int start = 0; int end = 0;
		 * 
		 * while (end < N * N) { end = start + N; int [] tmp =
		 * Arrays.copyOfRange(game, start, end); Arrays.sort(tmp);
		 * 
		 * for (int i = start; i < end; i++) { if (tmp[i % N]!=0 && tmp[i % N]
		 * == tmp[(i + 1) % N] && tmp[(i + 1) % N]!=0) { return false; } } start
		 * += N; } return true;
		 */
	}

	/*
	 * private boolean isValidHorizontal(int y, int number) { for (int i = y *
	 * N; i < (y + 1) * N; i++)
	 * 
	 * { if (game[i] == number) { return false; } } return true; } private
	 * boolean isValidVertical(int x, int number) { for (int i = x; i <
	 * game.length; i += N) { if (game[i] == number) { return false; } } return
	 * true; }
	 */

	public static void main(String[] args) {

		// int[] zeros = new int[9];
		int[] game1 = { 1, 2, 3, 4, 5, 6, 7, 8, 9 };
		int[] game2 = { 9, 2, 3, 4, 5, 6, 7, 1, 8 };
		int[] game3 = { 1, 1, 2, 3, 4, 5, 6, 7, 8 };

		// SudokuGame sg0 = new SudokuGame(3, zeros);
		SudokuGame_Kimberley sg1 = new SudokuGame_Kimberley(3, game1);
		SudokuGame_Kimberley sg2 = new SudokuGame_Kimberley(3, game2);
		SudokuGame_Kimberley sg3 = new SudokuGame_Kimberley(3, game3);
		// System.out.println("validHorizontal - " + sg1.isValidHorizontal(0,
		// 3));
		// System.out.println("validVertical - " + sg1.isValidVertical(0, 5));

		// System.out.println("All zero:" + sg0.isValidBoard());
		System.out.println("All unique - sorted: " + sg1.isValidBoard());
		System.out.println("All unique - not sorted: " + sg2.isValidBoard());
		System.out.println("NOT unique - not sorted: " + sg3.isValidBoard());

	}

}
