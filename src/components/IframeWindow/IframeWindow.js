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
    debugger;
    return (
      <Window
        {...props}
        className={cx("IframeWindow", {
          "Window--active": props.isActive
        })}
        initialHeight={props.data.height || 380}
        initialWidth={props.data.width || 440}
        menuOptions={props.data.useMenu && buildMenu(props)}
        Component={WindowProgram}
        resizable={!(props.data.width || props.data.height)}
      >
        <div style={props.data && props.data.style}>
          <iframe src={props.data.src} title={props.title} />
        </div>
      </Window>
    );
  }
}

export default IFrame;
