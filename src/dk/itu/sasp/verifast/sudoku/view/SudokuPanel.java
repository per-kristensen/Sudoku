package dk.itu.sasp.verifast.sudoku.view;

import java.awt.Color;
import java.awt.GridLayout;

import javax.swing.BorderFactory;
import javax.swing.JPanel;

import dk.itu.sasp.verifast.sudoku.controller.SudokuController;
import dk.itu.sasp.verifast.sudoku.model.Board;

public class SudokuPanel extends JPanel {
	private Field[][] fields;
	private JPanel[][] panels;

	public SudokuPanel() {
		super(new GridLayout(3, 3));

		panels = new JPanel[3][3];
		for (int x = 0; x < 3; x++) {
			for (int y = 0; y < 3; y++) {
				panels[x][y] = new JPanel(new GridLayout(3, 3));
				panels[x][y].setBorder(BorderFactory
						.createLineBorder(Color.DARK_GRAY));
				add(panels[x][y]);
			}
		}

		fields = new Field[9][9];
		for (int y = 0; y < 9; y++) {
			for (int x = 0; x < 9; x++) {
				fields[x][y] = new Field(x, y);
				panels[y / 3][x / 3].add(fields[x][y]);
			}
		}
	}

	public void setNumber(int x, int y, int number) {
		fields[x][y].setText("" + number);
	}

	public void setGame(Board game) {
		for (int x = 0; x < 9; x++) {
			for (int y = 0; y < 9; y++) {
				// fields[x][y].setText(game.getNumber(x, y) == 0 ? "" : "" +
				// game.getNumber(x, y));
				// fields[x][y].setBackground(Color.WHITE);
			}
		}
	}

	public void addActionListeners(SudokuController sudokuController) {
		for (int x = 0; x < 9; x++) {
			for (int y = 0; y < 9; y++) {
				fields[x][y].addActionListener(sudokuController);
			}
		}
	}

	public void checkGame(boolean[][] checkGame) {
		for (int x = 0; x < 9; x++) {
			for (int y = 0; y < 9; y++) {
				if (checkGame[x][y] == false)
					fields[x][y].setBackground(Color.RED);
				else
					fields[x][y].setBackground(Color.WHITE);
			}
		}
	}

}