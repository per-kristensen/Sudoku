package dk.itu.sasp.verifast.sudoku.controller;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.JMenuItem;

import dk.itu.sasp.verifast.sudoku.model.SudokuGame;
import dk.itu.sasp.verifast.sudoku.view.Field;
import dk.itu.sasp.verifast.sudoku.view.SudokuPanel;

public class SudokuController implements ActionListener {
	private SudokuPanel sudokuPanel;
	private SudokuGame game;

	public SudokuController(SudokuPanel sudokuPanel, SudokuGame game) {
		this.sudokuPanel = sudokuPanel;
		this.game = game;
	}

	@Override
	public void actionPerformed(ActionEvent e) {
		Object source = e.getSource();
		if (source instanceof Field) {
			Field field = (Field) e.getSource();
			int x = field.getFieldX();
			int y = field.getFieldY();
			int number = Integer.parseInt(field.getText());

			if (isValidInput(field.getText())) {
				game.setNumber(x, y, number);
				sudokuPanel.setNumber(x, y, number);
			} else {
				field.setText("");
			}
		} else if (source instanceof JMenuItem) {
			String menuItemText = ((JMenuItem) source).getText();
			if (menuItemText.equalsIgnoreCase("new game")) {
				this.game = new SudokuGame();
				setGame();
				System.out.println(game.printSolution());
			} else if (menuItemText.equalsIgnoreCase("check game")) {
				sudokuPanel.checkGame(this.game.checkGame());
			}

		}
	}

	private static boolean isValidInput(String str) {
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

	public void setGame() {
		sudokuPanel.setGame(game);
	}
}
