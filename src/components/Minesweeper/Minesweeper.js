import React, { Component } from "react";
import cx from "classnames";
import { WindowProgram } from "packard-belle";
import Minesweeper95 from "pb-minesweeper";

import { minesweeper16 } from "../../icons";
import buildMenu from "../../helpers/menuBuilder";

import Window from "../tools/Window";

import "./_styles.scss";

class Minesweeper extends Component {
  static defaultProps = {
    data: {}
  };
  state = {
    gameId: Date.now()
  };

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
          menuOptions={buildMenu({
            ...props,
            fileOptions: [
              {
                title: "Restart Game",
                onClick: () => this.setState({ gameId: Date.now() })
              }
            ],
            multiInstance: true
          })}
          className={cx("Minesweeper", props.className, {
            "Minesweeper--wrap": state.wrap,
            "Window--blocked": state.saveScreen
          })}
          title={`Minesweeper`}
          Component={WindowProgram}
          minHeight={150}
          minWidth={150}
          initialHeight={200}
          initialWidth={200}
          resizable={false}
          onMaximize={null}
        >
          <Minesweeper95 key={this.state.gameId} />
        </Window>
      </>
    );
  }
}

export default Minesweeper;
