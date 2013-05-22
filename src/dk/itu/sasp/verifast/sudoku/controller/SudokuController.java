package dk.itu.sasp.verifast.sudoku.controller;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.JMenuItem;

import dk.itu.sasp.verifast.sudoku.model.Board;
import dk.itu.sasp.verifast.sudoku.view.Field;
import dk.itu.sasp.verifast.sudoku.view.SudokuPanel;

public class SudokuController implements ActionListener {
	private SudokuPanel sudokuPanel;
	private Board game;

	public SudokuController(SudokuPanel sudokuPanel, Board game) {
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

			// TODO - calls to Board

		} else if (source instanceof JMenuItem) {
			String menuItemText = ((JMenuItem) source).getText();
			if (menuItemText.equalsIgnoreCase("new game")) {
				// TODO
			} else if (menuItemText.equalsIgnoreCase("check game")) {
				// TODO
			}

		}
	}

	public void setGame() {
		sudokuPanel.setGame(game);
	}
}
