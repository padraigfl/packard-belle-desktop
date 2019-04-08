import React, { Component } from "react";
import { WindowProgram, WindowAlert } from "packard-belle";
import cx from "classnames";
import { buildMenu } from "../ExplorerWindow/ExplorerWindow";
import "./_styles.scss";
import Window from "../tools/Window";

class IFrame extends Component {
  state = {
    displayAlert: this.props.data.displayAlert || true
  };

  confirm = () => this.setState({ displayAlert: false });

  render() {
    const { props, state } = this;

    const commonProps = {
      title: props.title,
      icon: props.icon,
      onClose: () => props.onClose(props.id)
    };

    if (state.displayAlert) {
      return (
        <WindowAlert
          {...commonProps}
          onOK={this.confirm}
          onCancel={commonProps.onClose}
          className="IframeWindow--alert"
        >
          {props.data.disclaimer ||
            `The Following is an iframe displaying, content belongs to the original creator at ${
              props.data.src
            }`}
        </WindowAlert>
      );
    }

    return (
      <Window
        {...props}
        className={cx("IframeWindow", {
          "Window--active": props.isActive
        })}
        initialHeight={380}
        initialWidth={440}
        menuOptions={props.data.useMenu && buildMenu(props)}
        Component={WindowProgram}
      >
        <iframe src={props.data.src} title={props.title} />
      </Window>
    );
  }
}

export default IFrame;
