package dk.itu.sasp.verifast.sudoku.controller;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

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
		Field field = (Field) e.getSource();

		if (SudokuGame.isValidInput(field.getText())) {
			game.setNumber(field.getFieldX(), field.getFieldY(), Integer.parseInt(field.getText()));
		} else {
			field.setText("");
		}
	}
}
