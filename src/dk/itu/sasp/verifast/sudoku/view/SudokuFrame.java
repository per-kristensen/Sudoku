package dk.itu.sasp.verifast.sudoku.view;

import java.awt.Dimension;
import java.awt.Toolkit;

import javax.swing.JFrame;

import dk.itu.sasp.verifast.sudoku.controller.SudokuController;
import dk.itu.sasp.verifast.sudoku.model.SudokuGame;

public class SudokuFrame extends JFrame {

	public SudokuFrame() {
		try {
			initFrame();
		} catch (Exception e) {
			e.printStackTrace();
		}

		Dimension screenSize = Toolkit.getDefaultToolkit().getScreenSize();
		Dimension frameSize = this.getSize();
		if (frameSize.height > screenSize.height) {
			frameSize.height = screenSize.height;
		}
		if (frameSize.width > screenSize.width) {
			frameSize.width = screenSize.width;
		}
		this.setLocation((screenSize.width - frameSize.width) / 2,
				(screenSize.height - frameSize.height) / 2);
		this.setVisible(true);
	}

	private void initFrame() throws Exception {
		this.setTitle("Sudoku with VeriFast");
		this.setSize(500, 500);
		this.setResizable(false);
		this.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);

		SudokuGame game = new SudokuGame();
		SudokuPanel sudokuPanel = new SudokuPanel();
		SudokuController sudokuController = new SudokuController(sudokuPanel,
				game);

		sudokuPanel.addActionListeners(sudokuController);

		this.getContentPane().add(sudokuPanel);
	}

	public static void main(String[] args) {
		new SudokuFrame();
	}

}