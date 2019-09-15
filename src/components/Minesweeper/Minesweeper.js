import React, { Component } from "react";
import cx from "classnames";
import { WindowProgram } from "packard-belle";
import Minesweeper95 from "pb-minesweeper";

import { minesweeper16 } from "../../icons";
import { helpOptions } from "../../helpers/menuBuilder";

import Window from "../tools/Window";

import "./_styles.scss";

const difficulty = {
  beginner: {
    gridSize: [9, 9],
    mines: 10
  },
  intermediate: {
    gridSize: [16, 16],
    mines: 40
  },
  expert: {
    gridSize: [30, 16],
    mines: 99
  }
};

class Minesweeper extends Component {
  static defaultProps = {
    data: {}
  };
  state = {
    gameId: Date.now(),
    difficulty: "beginner"
  };

  updateDifficulty = difficulty => () =>
    this.setState({ difficulty, gameId: Date.now() });

  render() {
    const { props, state } = this;
    return (
      <>
        <Window
          {...props}
          icon={minesweeper16}
          footer={[
            { text: "needs 100% width height" },
            { text: "overflow control" }
          ]}
          menuOptions={[
            {
              title: "File",
              options: [
                {
                  title: "New",
                  onClick: () => this.setState({ gameId: Date.now() })
                },
                [
                  ...Object.keys(difficulty).map(level => ({
                    title: level[0].toUpperCase() + level.slice(1),
                    onClick: this.updateDifficulty(level),
                    className:
                      this.state.difficulty === level ? "checked" : undefined
                  })),
                  { title: "Custom", isDisabled: true }
                ],
                { title: "Close", onClick: () => props.onClose(props) }
              ]
            },
            helpOptions(props)
          ]}
          className={cx("Minesweeper", props.className, {
            "Minesweeper--wrap": state.wrap,
            "Window--blocked": state.saveScreen
          })}
          title={`Minesweeper`}
          Component={WindowProgram}
          minHeight={150}
          minWidth={150}
          initialHeight={150}
          initialWidth={150}
          resizable={false}
          onMaximize={null}
        >
          <Minesweeper95
            key={this.state.gameId}
            {...difficulty[this.state.difficulty]}
          />
        </Window>
      </>
    );
  }
}

export default Minesweeper;
