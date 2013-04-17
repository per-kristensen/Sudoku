package dk.itu.sasp.verifast.sudoku.model;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public class SudokuGame {
	private int[][] solution;
	private int[][] game;

	public SudokuGame() {
		newGame();
	}

	public void newGame() {
		solution = generateSolution(new int[9][9], 0);
		game = generateGame(copy(solution));
	}

	private int[][] generateSolution(int[][] game, int index) {
		if (index > 80)
			return game;

		int x = index % 9;
		int y = index / 9;

		List<Integer> numbers = new ArrayList<Integer>();
		for (int i = 1; i <= 9; i++)
			numbers.add(i);
		Collections.shuffle(numbers);

		while (numbers.size() > 0) {
			int number = getNextPossibleNumber(game, x, y, numbers);
			if (number == -1)
				return null;

			game[x][y] = number;
			int[][] tmpGame = generateSolution(game, index + 1);
			if (tmpGame != null)
				return tmpGame;
			game[x][y] = 0;
		}

		return null;
	}

	private int[][] generateGame(int[][] game) {
		List<Integer> positions = new ArrayList<Integer>();
		for (int i = 0; i < 81; i++)
			positions.add(i);
		Collections.shuffle(positions);
		return generateGame(game, positions);
	}

	private int[][] generateGame(int[][] game, List<Integer> positions) {
		while (positions.size() > 0) {
			int position = positions.remove(0);
			int x = position % 9;
			int y = position / 9;
			int temp = game[x][y];
			game[x][y] = 0;

			if (!isValid(game))
				game[x][y] = temp;
		}

		return game;
	}

	public boolean[][] checkGame() {
		boolean[][] check = new boolean[9][9];
		for (int x = 0; x < 9; x++) {
			for (int y = 0; y < 9; y++) {
				if (solution[x][y] == game[x][y])
					check[x][y] = true;
			}
		}
		return check;
	}

	private int getNextPossibleNumber(int[][] game, int x, int y,
			List<Integer> numbers) {
		while (numbers.size() > 0) {
			int number = numbers.remove(0);
			if (isValidMove(game, x, y, number))
				return number;
		}
		return -1;
	}

	private boolean isValid(int[][] game) {
		return isValid(game, 0, new int[] { 0 });
	}

	private boolean isValid(int[][] game, int index, int[] numberOfSolutions) {
		if (index > 80)
			return ++numberOfSolutions[0] == 1;

		int x = index % 9;
		int y = index / 9;

		if (game[x][y] == 0) {
			List<Integer> numbers = new ArrayList<Integer>();
			for (int i = 1; i <= 9; i++)
				numbers.add(i);

			while (numbers.size() > 0) {
				int number = getNextPossibleNumber(game, x, y, numbers);
				if (number == -1)
					break;
				game[x][y] = number;

				if (!isValid(game, index + 1, numberOfSolutions)) {
					game[x][y] = 0;
					return false;
				}
				game[x][y] = 0;
			}
		} else if (!isValid(game, index + 1, numberOfSolutions))
			return false;

		return true;
	}

	private int[][] copy(int[][] game) {
		int[][] copy = new int[9][9];
		for (int y = 0; y < 9; y++) {
			for (int x = 0; x < 9; x++)
				copy[x][y] = game[x][y];
		}
		return copy;
	}

	public String printSolution() {
		String solution = "";
		for (int y = 0; y < 9; y++) {
			solution += "\n";
			for (int x = 0; x < 9; x++) {
				solution += this.solution[x][y] + "\t";
			}
		}
		return solution;
	}

	public void setNumber(int x, int y, int number) {
		game[x][y] = number;
	}

	private boolean isValidVertical(int[][] game, int x, int number) {

		for (int y = 0; y < 9; y++) {
			if (game[x][y] == number) {
				return false;
			}
		}
		return true;
	}

	private boolean isValidHorionzotal(int[][] game, int y, int number) {
		for (int x = 0; x < 9; x++) {
			if (game[x][y] == number) {
				return false;
			}
		}
		return true;
	}

	private boolean isValidBlock(int[][] game, int x, int y, int number) {
		int x1 = x < 3 ? 0 : x < 6 ? 3 : 6;
		int y1 = y < 3 ? 0 : y < 6 ? 3 : 6;

		for (int yy = y1; yy < y1 + 3; yy++) {
			for (int xx = x1; xx < x1 + 3; xx++) {
				if (game[xx][yy] == number) {
					return false;
				}
			}
		}
		return true;
	}

	public boolean isValidMove(int[][] game, int x, int y, int number) {
		return isValidHorionzotal(game, y, number)
				&& isValidVertical(game, x, number)
				&& isValidBlock(game, x, y, number);
	}

	public int getNumber(int x, int y) {
		return game[x][y];
	}
}
